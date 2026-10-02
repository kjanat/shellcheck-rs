#!/usr/bin/env python3
import re
import sys
import unicodedata
from pathlib import Path

REPO = "https://github.com/kjanat/shellcheck-rs"
UPSTREAM = "https://github.com/koalaman/shellcheck"
PAGE = re.compile(r"^(\d{2}) (.+)\.md$")
NUMBERED = re.compile(r"^\d+(?:\.\d+)*\s+")


def slug(text):
    text = re.sub(r"\]\[[^\]]*\]|\]\([^)]*\)", "]", text)
    kept = (
        c
        for c in text.lower()
        if c.isalnum() or c in " -_" or unicodedata.category(c).startswith("M")
    )
    return "".join(kept).replace(" ", "-")


def label(text):
    text = re.sub(r"\[([^\]]*)\]\[[^\]]*\]", r"\1", text)
    return re.sub(r"\[([^\]]*)\]", r"\1", text).strip()


def renumber(path, n, title):
    lines = path.read_text().split("\n")
    sections = []
    fence = False
    k = 0
    for i, line in enumerate(lines):
        if line.startswith("```"):
            fence = not fence
        if fence:
            continue
        if line.startswith("# "):
            lines[i] = f"# {n} {title}"
        elif line.startswith("## "):
            k += 1
            text = NUMBERED.sub("", line[3:].strip())
            heading = f"{n}.{k} {text}"
            lines[i] = f"## {heading}"
            sections.append((heading, label(text)))
    path.write_text("\n".join(lines))
    return sections


SEPARATOR = "&ensp;·&ensp;"


def sidebar(index, current):
    lines = ["**[Home](Home)**" if current is None else "[Home](Home)", ""]
    for n, url, title, sections in index:
        entry = f"[{title}]({url})"
        lines.append(f"{n}. **{entry}**" if n == current else f"{n}. {entry}")
        if n == current:
            for heading, text in sections:
                number = heading.split(" ", 1)[0]
                lines.append(f"   - [{number} {text}]({url}#{slug(heading)})")
    lines += ["", '<sub><a href="#idend">↓ End of page</a></sub>']
    return "\n".join(lines) + "\n"


def footer(prev, nxt, home):
    links = []
    if prev:
        links.append(f'<a href="{prev[0]}">← {prev[1]}</a>')
    if not home:
        links.append('<a href="Home">Home</a>')
    if nxt:
        links.append(f'<a href="{nxt[0]}">{nxt[1]} →</a>')
    colophon = [
        '<a href="#idtop">Top</a>',
        f'<a href="{REPO}">shellcheck-rs</a>',
        f'<a href="{UPSTREAM}">upstream ShellCheck</a>',
        "© 2026 Kaj Kowalski",
    ]
    return (
        f'<p align="center">{SEPARATOR.join(links)}</p>\n\n'
        f'<p align="center"><sub>{SEPARATOR.join(colophon)}</sub></p>\n'
    )


def main():
    wiki = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path(__file__).resolve().parent.parent
    )
    index = []
    for folder in sorted(wiki.glob("[0-9][0-9]-0000")):
        pages = [(p, m) for p in folder.glob("*.md") if (m := PAGE.match(p.name))]
        if len(pages) != 1:
            sys.exit(
                f"{folder.name}: expected one page named 'NN Title.md', found {[p.name for p, _ in pages]}"
            )
        page, match = pages[0]
        number, title = match.groups()
        if folder.name != f"{number}-0000":
            sys.exit(
                f"{page}: page number {number} does not match folder {folder.name}"
            )
        n = int(number)
        index.append((n, page.stem.replace(" ", "-"), title, renumber(page, n, title)))
    if not index:
        sys.exit(f"{wiki}: no NN-0000 page folders")

    targets = [(url, f"{n} {title}") for n, url, title, _ in index]
    (wiki / "_Sidebar.md").write_text(sidebar(index, None))
    (wiki / "_Footer.md").write_text(footer(None, targets[0], True))
    for i, (n, _, _, _) in enumerate(index):
        prev = targets[i - 1] if i > 0 else None
        nxt = targets[i + 1] if i + 1 < len(targets) else None
        folder = wiki / f"{n:02d}-0000"
        (folder / "_Sidebar.md").write_text(sidebar(index, n))
        (folder / "_Footer.md").write_text(footer(prev, nxt, False))


main()
