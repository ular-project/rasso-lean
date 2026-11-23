#!/usr/bin/env python3
"""Checks of a Markdown blueprint. The release ships this as tools/check-blueprint-md.py.

  check.py MD-DIR [--also FILE ...] [--lean-dir DIR] [--files LIST] [--list-external]

Reads only the Markdown. Exit 1 on any failure. Each check, and why:

* links: every relative link resolves from the folder of the page that holds it. A link
  to a checked page (MD-DIR's pages, and each --also FILE) must find its id there: an
  explicit <a id="..."> or the slug GitHub makes from a heading. A link to any other file
  or folder must exist, the PDF included. LICENSE is the one exception, since the
  release's LICENSE is kept by the publish and not written by the export;
* Lean links: every link into the Lean code names a file that exists (under --lean-dir,
  or in --files, the list of files that ship), with its lines inside the file;
* ids: no two equal on a page, and no colon in an id or a link's fragment (GitHub drops
  the colon from an id, so the link would miss);
* external links are not followed. --list-external prints each once, with its pages;
* the entry page's contents have no math (GitHub renders none in a list of links);
* no known silent defect, where GitHub renders a page without error but wrongly: plain $
  outside the $`...`$ form; a GitHub footnote [^ (numbered per page); a fenced math block
  inside <details>; \\texttt{ holding \\_; math ending an emphasis; a bare | in a table
  cell's math.
"""
import argparse
import os
import re
import sys

LINK = re.compile(r"(?<!!)\[(?:[^\[\]]|\[[^\]]*\])*\]\(([^)\s]*)\)")
ANCHOR = re.compile(r'<a id="([^"]+)"')
HEADING = re.compile(r"^(#{1,6}) (.*)$", re.M)
SPAN = re.compile(r"\$`.*?`\$")
FENCE = re.compile(r"^```.*?^```", re.S | re.M)


def github_slug(title):
    t = re.sub(r"\$`.*?`\$", lambda m: m.group(0)[2:-2], title)
    t = re.sub(r"<[^>]+>", "", t).lower()
    t = re.sub(r"[^\w\- ]", "", t)
    return t.replace(" ", "-")


def without_code(text):
    """The text without fenced blocks and code spans, which Markdown leaves alone."""
    text = FENCE.sub("", text)
    return re.sub(r"(?<!\$)`[^`\n]*`(?!\$)", "", text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("md")
    ap.add_argument("--also", nargs="*", default=[], help="pages outside MD-DIR to check too")
    ap.add_argument("--lean-dir", default=None, help="the folder that Lean links are relative to")
    ap.add_argument("--files", default=None, help="a file listing the Lean files that ship")
    ap.add_argument("--list-external", action="store_true", help="print the external links")
    a = ap.parse_args()
    # A page is named by its path, so that a link resolves from the page's own folder.
    names = [os.path.join(a.md, f) for f in sorted(os.listdir(a.md)) if f.endswith(".md")]
    names += a.also
    pages = {os.path.normpath(f): open(f, encoding="utf-8").read() for f in names}
    entry = os.path.normpath(os.path.join(a.md, "README.md"))
    shipped = set(open(a.files).read().split()) if a.files else None
    fails = []
    ids = {}
    # Block quotes (theorem statements) hold fences too: read them without the quote marks.
    pages = {p: re.sub(r"(?m)^(?:> ?)+", "", t) for p, t in pages.items()}
    for p, text in pages.items():
        found = ANCHOR.findall(text)
        dup = {x for x in found if found.count(x) > 1}
        if dup:
            fails.append(f"{p}: ids twice: {sorted(dup)[:5]}")
        slugs = {github_slug(h) for _, h in HEADING.findall(FENCE.sub("", text))}
        ids[p] = set(found) | slugs
        for x in found:
            if ":" in x:
                fails.append(f"{p}: an id with a colon: {x}")
    nlinks = nlean = 0
    external = {}
    for p, text in pages.items():
        for target in LINK.findall(without_code(SPAN.sub("", text))):
            if re.match(r"^[a-z]+:", target):
                external.setdefault(target, set()).add(p)
                continue
            path, _, frag = target.partition("#")
            if ":" in frag:
                fails.append(f"{p}: a link fragment with a colon: {target}")
            if path.endswith(".lean"):
                nlean += 1
                rel = os.path.normpath(path.replace("../", "", 1)) if path.startswith("../") else path
                if shipped is not None and rel not in shipped:
                    fails.append(f"{p}: a Lean link to a file that does not ship: {target}")
                    continue
                if a.lean_dir:
                    f = os.path.join(a.lean_dir, rel)
                    if not os.path.exists(f):
                        fails.append(f"{p}: a Lean link to a missing file: {target}")
                        continue
                    n = sum(1 for _ in open(f, encoding="utf-8"))
                    m = re.fullmatch(r"L(\d+)(?:-L(\d+))?", frag)
                    if not m or int(m.group(2) or m.group(1)) > n or int(m.group(1)) > int(m.group(2) or m.group(1)):
                        fails.append(f"{p}: Lean lines outside the file: {target}")
                continue
            nlinks += 1
            page = os.path.normpath(os.path.join(os.path.dirname(p), path)) if path else p
            if page in pages:
                if frag and frag not in ids[page]:
                    fails.append(f"{p}: a link to an unknown id: {target}")
            elif os.path.basename(page) == "LICENSE":
                pass
            elif not os.path.exists(page):
                fails.append(f"{p}: a link to a missing file: {target}")
    contents = pages.get(entry, "").split("## Contents", 1)[-1]
    if SPAN.search(contents):
        fails.append(f"{entry}: math in the contents")
    for p, text in pages.items():
        bare = without_code(SPAN.sub("", text))
        for m in re.finditer(r"(?<!\\)\$", bare):
            fails.append(f"{p}: a plain $: ...{bare[max(0, m.start()-30):m.start()+30]!r}")
            break
        if "[^" in bare:
            fails.append(f"{p}: a GitHub footnote")
        for d in re.findall(r"<details>.*?</details>", text, re.S):
            if "```math" in d:
                fails.append(f"{p}: display math inside <details>")
        for s in SPAN.findall(text):
            if re.search(r"\\texttt\{[^}]*\\_", s):
                fails.append(f"{p}: \\texttt holding \\_: {s}")
        if re.search(r"`\$[*_]", text):
            fails.append(f"{p}: math ending an emphasis")
        for line in text.splitlines():
            if line.startswith("|"):
                for s in SPAN.findall(line):
                    if re.search(r"(?<!\\)\|", s):
                        fails.append(f"{p}: a bare | in a table cell's math: {s}")
    if a.list_external:
        for url in sorted(external):
            print(f"external {url}  ({', '.join(sorted(external[url]))})")
    for f in fails:
        print("FAIL " + f)
    print(f"{len(pages)} pages, {nlinks} links and {nlean} Lean links checked, {len(external)} external links not followed, {len(fails)} failures")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
