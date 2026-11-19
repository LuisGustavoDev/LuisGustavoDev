#!/usr/bin/env python3
"""
Card "linguagens mais usadas" a partir dos SEUS commits, em todos os repositórios
(seus, privados, de organizações e de terceiros), de forma incremental.

- Descobre os repositórios em que você tem commits (contribuições de todos os anos
  + repositórios seus + repositórios para os quais contribuiu).
- Na primeira execução analisa o histórico inteiro; depois, só os repositórios que
  receberam push desde a última execução e só os commits novos (nunca conta duas vezes).
- Conta as linhas ADICIONADAS por você em cada arquivo (git log --numstat), na branch
  padrão (a mesma regra que o GitHub usa para contar contribuições).
- Guarda o progresso em profile/langs-state.json. Nomes de repositórios e SHAs são
  gravados só como hash, para não expor repositórios privados num repo público.

Só usa a biblioteca padrão do Python e o git do runner.

Variáveis de ambiente:
  GH_TOKEN        token clássico com escopos repo, read:org, read:user (obrigatório)
  GH_USER         seu usuário do GitHub
  AUTHOR_EMAILS   e-mails que você usa nos commits, separados por vírgula
  AUTHOR_NAMES    nomes de autor (opcional), separados por vírgula
  IGNORED_LANGS   linguagens a esconder do card, separadas por vírgula
  LANGS_COUNT     quantas linguagens mostrar (padrão 6)
  CARD_TITLE      título do card
  STATE_PATH      padrão profile/langs-state.json
  OUT_PATH        padrão profile/top-langs.svg
  FULL=1          ignora o estado e refaz tudo do zero
"""
import base64
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from html import escape

TOKEN = os.environ.get("GH_TOKEN", "").strip()
USER = os.environ.get("GH_USER", "").strip()
EMAILS = {e.strip().lower() for e in os.environ.get("AUTHOR_EMAILS", "").split(",") if e.strip()}
NAMES = {n.strip().lower() for n in os.environ.get("AUTHOR_NAMES", "").split(",") if n.strip()}
IGNORED = {x.strip().lower() for x in os.environ.get("IGNORED_LANGS", "").split(",") if x.strip()}
LANGS_COUNT = int(os.environ.get("LANGS_COUNT", "6"))
TITLE = os.environ.get("CARD_TITLE", "Most Used Languages")
STATE_PATH = os.environ.get("STATE_PATH", "profile/langs-state.json")
OUT_PATH = os.environ.get("OUT_PATH", "profile/top-langs.svg")
FULL = os.environ.get("FULL", "") == "1"
BASE_URL = os.environ.get("GIT_BASE_URL", "https://github.com/")  # só para testes locais

# Janela de sobreposição nas execuções incrementais (commits já contados são pulados pelo hash).
OVERLAP_DAYS = 3
# Um arquivo com mais linhas adicionadas que isso num único commit é tratado como gerado/copiado.
MAX_LINES_PER_FILE = 3000

if USER:
    NAMES.add(USER.lower())
NOREPLY = re.compile(r"^(\d+\+)?%s@users\.noreply\.github\.com$" % re.escape(USER.lower())) if USER else None

# ---------------------------------------------------------------- linguagens
EXT = {
    "ts": "TypeScript", "mts": "TypeScript", "cts": "TypeScript", "tsx": "TypeScript",
    "js": "JavaScript", "mjs": "JavaScript", "cjs": "JavaScript", "jsx": "JavaScript",
    "py": "Python", "pyi": "Python", "ipynb": "Jupyter Notebook",
    "java": "Java", "kt": "Kotlin", "kts": "Kotlin", "scala": "Scala", "groovy": "Groovy",
    "php": "PHP", "go": "Go", "rs": "Rust", "rb": "Ruby", "ex": "Elixir", "exs": "Elixir",
    "c": "C", "h": "C", "cpp": "C++", "cc": "C++", "cxx": "C++", "hpp": "C++", "hh": "C++",
    "cs": "C#", "swift": "Swift", "dart": "Dart", "lua": "Lua", "r": "R", "jl": "Julia",
    "vue": "Vue", "svelte": "Svelte", "astro": "Astro",
    "sql": "SQL", "prisma": "Prisma", "graphql": "GraphQL", "gql": "GraphQL",
    "sh": "Shell", "bash": "Shell", "zsh": "Shell", "ps1": "PowerShell",
    "html": "HTML", "htm": "HTML", "css": "CSS", "scss": "SCSS", "sass": "Sass", "less": "Less",
    "ejs": "EJS", "hbs": "Handlebars", "twig": "Twig", "liquid": "Liquid", "sol": "Solidity",
}
FILENAMES = {"dockerfile": "Dockerfile", "makefile": "Makefile"}
COLORS = {
    "TypeScript": "#3178c6", "JavaScript": "#f1e05a", "Python": "#3572A5", "Jupyter Notebook": "#DA5B0B",
    "Java": "#b07219", "Kotlin": "#A97BFF", "Scala": "#c22d40", "Groovy": "#4298b8", "PHP": "#4F5D95",
    "Blade": "#f7523f", "Go": "#00ADD8", "Rust": "#dea584", "Ruby": "#701516", "Elixir": "#6e4a7e",
    "C": "#555555", "C++": "#f34b7d", "C#": "#178600", "Swift": "#F05138", "Dart": "#00B4AB",
    "Lua": "#000080", "R": "#198CE7", "Julia": "#a270ba", "Vue": "#41b883", "Svelte": "#ff3e00",
    "Astro": "#ff5a03", "SQL": "#e38c00", "Prisma": "#5a67d8", "GraphQL": "#e10098", "Shell": "#89e051",
    "PowerShell": "#012456", "HTML": "#e34c26", "CSS": "#563d7c", "SCSS": "#c6538c", "Sass": "#a53b70",
    "Less": "#1d365d", "EJS": "#a91e50", "Handlebars": "#f7931e", "Twig": "#c1d026", "Liquid": "#67b8de",
    "Solidity": "#AA6746", "Dockerfile": "#384d54", "Makefile": "#427819",
}
SKIP_DIR = re.compile(
    r"(^|/)(node_modules|vendor|dist|build|out|\.next|\.nuxt|coverage|__pycache__|\.venv|venv|"
    r"site-packages|bower_components|public/build|storage/framework|prisma/migrations|"
    # WordPress: núcleo, plugins, uploads e cache não são código seu
    r"wp-admin|wp-includes|wp-content/plugins|wp-content/mu-plugins|wp-content/uploads|wp-content/cache|"
    r"wp-content/upgrade|wp-content/languages|"
    # bibliotecas de terceiros copiadas para o projeto
    r"third[-_]party|assets/vendor|assets/libs?|static/vendor|js/vendor|css/vendor|plugins/vendor)/"
)
# Um commit que adiciona mais linhas que isso de uma vez é importação (site inteiro, scaffold, cópia).
MAX_LINES_PER_COMMIT = 10000
SKIP_FILE = re.compile(r"(\.min\.(js|css)|\.d\.ts|\.map|-lock\.\w+|\.lock|\.bundle\.js|\.chunk\.js)$")


def language_of(path):
    p = path.lower()
    if SKIP_DIR.search(p) or SKIP_FILE.search(p):
        return None
    name = p.rsplit("/", 1)[-1]
    if name in FILENAMES or name.startswith("dockerfile"):
        return FILENAMES.get(name, "Dockerfile")
    if name.endswith(".blade.php"):
        return "Blade"
    if "." not in name:
        return None
    return EXT.get(name.rsplit(".", 1)[-1])


def is_me(email, name):
    email, name = (email or "").lower(), (name or "").lower()
    return email in EMAILS or name in NAMES or bool(NOREPLY and NOREPLY.match(email))


def h(text):
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def log(*a):
    print(*a, flush=True)


# ---------------------------------------------------------------- GitHub API
def graphql(query, variables, tries=4):
    body = json.dumps({"query": query, "variables": variables}).encode()
    for attempt in range(tries):
        req = urllib.request.Request(
            "https://api.github.com/graphql", data=body,
            headers={"Authorization": f"bearer {TOKEN}", "Content-Type": "application/json"},
        )
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                data = json.load(r)
            if data.get("errors") and not data.get("data"):
                raise RuntimeError(data["errors"])
            for e in data.get("errors") or []:
                log("  aviso GraphQL:", e.get("message"))
            return data["data"]
        except (urllib.error.URLError, TimeoutError, RuntimeError) as e:
            if attempt == tries - 1:
                raise
            log(f"  GraphQL falhou ({e}); tentando de novo")
            time.sleep(3 * (attempt + 1))


REPO_FIELDS = "nameWithOwner pushedAt isEmpty isPrivate defaultBranchRef { name }"


def discover():
    repos = {}

    def add(node):
        if node and not node.get("isEmpty"):
            repos[node["nameWithOwner"]] = node

    created = graphql("query($l:String!){user(login:$l){createdAt}}", {"l": USER})["user"]["createdAt"]
    start = dt.datetime.fromisoformat(created.replace("Z", "+00:00"))
    now = dt.datetime.now(dt.timezone.utc)
    while start < now:
        end = min(start + dt.timedelta(days=365), now)
        q = """query($l:String!,$f:DateTime!,$t:DateTime!){user(login:$l){contributionsCollection(from:$f,to:$t){
               commitContributionsByRepository(maxRepositories:100){repository{%s}}}}}""" % REPO_FIELDS
        d = graphql(q, {"l": USER, "f": start.isoformat(), "t": end.isoformat()})
        for c in d["user"]["contributionsCollection"]["commitContributionsByRepository"]:
            add(c["repository"])
        start = end

    for field, args in (
        ("repositories", "ownerAffiliations:[OWNER]"),
        ("repositoriesContributedTo", "contributionTypes:[COMMIT], includeUserRepositories:true"),
    ):
        cursor = None
        while True:
            q = """query($c:String){viewer{%s(first:25, after:$c, %s){
                   nodes{%s} pageInfo{hasNextPage endCursor}}}}""" % (field, args, REPO_FIELDS)
            d = graphql(q, {"c": cursor})["viewer"][field]
            for n in d["nodes"]:
                add(n)
            if not d["pageInfo"]["hasNextPage"]:
                break
            cursor = d["pageInfo"]["endCursor"]
    return repos


USER_ID = None


def my_commits(repo, since):
    """SHAs da branch padrão que o GitHub atribui à sua conta (mesmo critério das contribuições)."""
    global USER_ID
    if USER_ID is None:
        USER_ID = graphql("query($l:String!){user(login:$l){id}}", {"l": USER})["user"]["id"]
    owner, name = repo.split("/", 1)
    shas, cursor = set(), None
    since_arg = ", since:$s" if since else ""
    q = """query($o:String!,$n:String!,$a:ID!,$c:String%s){repository(owner:$o,name:$n){defaultBranchRef{target{
           ... on Commit{history(first:100, after:$c, author:{id:$a}%s){nodes{oid} pageInfo{hasNextPage endCursor}}}}}}}""" % (
        ",$s:GitTimestamp!" if since else "", since_arg)
    while True:
        v = {"o": owner, "n": name, "a": USER_ID, "c": cursor}
        if since:
            v["s"] = since + "T00:00:00Z"
        ref = (graphql(q, v).get("repository") or {}).get("defaultBranchRef")
        if not ref:
            return shas
        hist = ref["target"]["history"]
        shas.update(n["oid"] for n in hist["nodes"])
        if not hist["pageInfo"]["hasNextPage"]:
            return shas
        cursor = hist["pageInfo"]["endCursor"]


def label(name, info):
    return f"🔒 privado-{h(name.lower())[:6]}" if info.get("isPrivate") else name


# ---------------------------------------------------------------- git
def git(args, cwd=None, timeout=900):
    auth = base64.b64encode(f"x-access-token:{TOKEN}".encode()).decode()
    cmd = ["git", "-c", f"http.https://github.com/.extraheader=AUTHORIZATION: basic {auth}", *args]
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                          env={**os.environ, "GIT_TERMINAL_PROMPT": "0"})


SKIPPED_BULK = []
RENAME_BRACES = re.compile(r"\{[^{}]* => ([^{}]*)\}")


def analyze(repo, since, seen, mine=frozenset()):
    """Retorna (linhas por linguagem, hashes dos commits novos)."""
    tmp = tempfile.mkdtemp(prefix="langs-")
    try:
        args = ["clone", "--bare", "--single-branch", "--quiet"]
        if since:
            args.append(f"--shallow-since={since}")
        r = git([*args, f"{BASE_URL}{repo}.git", tmp])
        if r.returncode != 0:
            if since and "shallow" in r.stderr.lower():
                return {}, []  # nenhum commit depois da data
            raise RuntimeError(r.stderr.strip().splitlines()[-1] if r.stderr.strip() else "clone falhou")

        boundary = set()
        shallow_file = os.path.join(tmp, "shallow")
        if since and os.path.exists(shallow_file):
            # Traz um commit a mais antes da janela, para que os commits novos tenham o pai
            # e o diff deles saia certo (o commit de borda é antigo e já foi contado antes).
            git(["fetch", "--quiet", "--deepen=1", "origin"], cwd=tmp)
        if os.path.exists(shallow_file):
            boundary = set(open(shallow_file).read().split())

        out = git(["log", "HEAD", "--no-merges", "-M", "--numstat",
                   "--format=%x1e%H%x1f%ae%x1f%an"], cwd=tmp).stdout
        totals, new = {}, []
        for block in out.split("\x1e")[1:]:
            header, _, body = block.partition("\n")
            sha, email, name = header.split("\x1f")
            if sha in boundary or not (sha in mine or is_me(email, name)):
                continue
            key = h(sha)
            if key in seen:
                continue
            new.append(key)
            commit_totals = {}
            for line in body.splitlines():
                parts = line.split("\t")
                if len(parts) != 3 or parts[0] == "-":
                    continue
                added, path = int(parts[0]), parts[2]
                if " => " in path:
                    path = RENAME_BRACES.sub(r"\1", path)
                    path = path.split(" => ")[-1].replace("//", "/")
                lang = language_of(path)
                if lang and 0 < added <= MAX_LINES_PER_FILE:
                    commit_totals[lang] = commit_totals.get(lang, 0) + added
            if sum(commit_totals.values()) > MAX_LINES_PER_COMMIT:
                SKIPPED_BULK.append(sha)
                continue
            for lang, v in commit_totals.items():
                totals[lang] = totals.get(lang, 0) + v
        return totals, new
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------- SVG (estilo tokyonight compacto)
def render(totals):
    shown = sorted(((l, v) for l, v in totals.items() if l.lower() not in IGNORED and v > 0),
                   key=lambda x: -x[1])[:LANGS_COUNT]
    total = sum(v for _, v in shown) or 1
    width, bar_w = 380, 330
    rows = (len(shown) + 1) // 2
    height = 90 + rows * 25

    bar, x = [], 0.0
    for lang, v in shown:
        w = bar_w * v / total
        bar.append(f'<rect mask="url(#rect-mask)" x="{x:.2f}" y="0" width="{w:.2f}" height="8" '
                   f'fill="{COLORS.get(lang, "#858585")}"/>')
        x += w

    legend = []
    for i, (lang, v) in enumerate(shown):
        col, row = i % 2, i // 2
        legend.append(
            f'<g transform="translate({col * 165}, {row * 25})">'
            f'<circle cx="5" cy="6" r="5" fill="{COLORS.get(lang, "#858585")}"/>'
            f'<text x="15" y="10" class="lang-name">{escape(lang)} {100 * v / total:.2f}%</text></g>'
        )

    return f"""<svg width="{width}" height="{height}" viewBox="0 0 {width} {height}" fill="none" xmlns="http://www.w3.org/2000/svg" role="img" aria-labelledby="title">
  <title id="title">{escape(TITLE)}</title>
  <style>
    .header {{ font: 600 18px 'Segoe UI', Ubuntu, Sans-Serif; fill: #70a5fd; }}
    .lang-name {{ font: 400 11px 'Segoe UI', Ubuntu, Sans-Serif; fill: #38bdae; }}
  </style>
  <rect x="0.5" y="0.5" rx="4.5" height="99%" width="{width - 1}" fill="#1a1b27" stroke-opacity="0"/>
  <g transform="translate(25, 35)"><text x="0" y="0" class="header">{escape(TITLE)}</text></g>
  <g transform="translate(25, 55)">
    <mask id="rect-mask"><rect x="0" y="0" width="{bar_w}" height="8" fill="white" rx="5"/></mask>
    {"".join(bar)}
    <g transform="translate(0, 25)">{"".join(legend)}</g>
  </g>
</svg>
"""


# ---------------------------------------------------------------- main
def main():
    if not TOKEN or not USER:
        sys.exit("Defina GH_TOKEN e GH_USER.")

    state = {"version": 1, "last_run": None, "commits": 0, "totals": {}, "repos": {}}
    if not FULL and os.path.exists(STATE_PATH):
        state = json.load(open(STATE_PATH))
    started = dt.datetime.now(dt.timezone.utc)
    log("Modo:", f"incremental (última execução: {state['last_run']})" if state.get("last_run") else "análise completa")

    repos = discover()
    log(f"Repositórios com commits seus: {len(repos)}")

    failures, added_commits = [], 0
    for name, info in sorted(repos.items()):
        key = h(name.lower())
        entry = state["repos"].setdefault(key, {"seen": []})
        pushed = dt.datetime.fromisoformat(info["pushedAt"].replace("Z", "+00:00")) if info.get("pushedAt") else None
        last = dt.datetime.fromisoformat(entry["last"]) if entry.get("last") else None

        if last and pushed and pushed < last:
            continue  # nenhum push desde a última análise deste repositório
        since = (last - dt.timedelta(days=OVERLAP_DAYS)).strftime("%Y-%m-%d") if last else None

        t0 = time.time()
        try:
            totals, new = analyze(name, since, set(entry["seen"]), my_commits(name, since))
        except Exception as e:  # noqa: BLE001
            failures.append(label(name, info))
            log(f"  ✗ {label(name, info)}: {e}")
            continue
        for lang, v in totals.items():
            state["totals"][lang] = state["totals"].get(lang, 0) + v
        entry["seen"].extend(new)
        entry["last"] = started.isoformat(timespec="seconds")
        added_commits += len(new)
        log(f"  ✓ {label(name, info)}: +{len(new)} commits ({'desde ' + since if since else 'histórico completo'}, {time.time() - t0:.0f}s)")

    state["commits"] = sum(len(e["seen"]) for e in state["repos"].values())
    state["last_run"] = started.isoformat(timespec="seconds")

    os.makedirs(os.path.dirname(OUT_PATH) or ".", exist_ok=True)
    with open(OUT_PATH, "w") as f:
        f.write(render(state["totals"]))
    with open(STATE_PATH, "w") as f:
        json.dump(state, f, indent=1, sort_keys=True)

    if SKIPPED_BULK:
        log(f"Commits de importação em massa ignorados (> {MAX_LINES_PER_COMMIT} linhas): {len(SKIPPED_BULK)}")
    log(f"\nCommits novos nesta execução: {added_commits} · total analisado: {state['commits']}")
    for lang, v in sorted(state["totals"].items(), key=lambda x: -x[1])[:12]:
        log(f"  {lang:<18} {v:>9} linhas{'  (escondida)' if lang.lower() in IGNORED else ''}")
    if failures:
        log(f"\n⚠ {len(failures)} repositório(s) não puderam ser lidos e serão tentados de novo na próxima execução:")
        for n in failures:
            log("  -", n)


if __name__ == "__main__":
    main()
