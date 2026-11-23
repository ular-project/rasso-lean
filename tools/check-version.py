#!/usr/bin/env python3
"""One version and one date across the release.

  python3 tools/check-version.py [--pdf FILE]

Run from the repository's root. The version comes from lakefile.toml (`version`), and
the date from CITATION.cff (`date-released`). It checks that CITATION.cff has the same
version, and that README.md and blueprint/README.md both say "Draft v<version>, <date>",
with the date written as "15 November 2026". With --pdf, the PDF's text (pdftotext,
from poppler) must say the same. Exit 1 on any failure.
"""
import datetime
import re
import subprocess
import sys

MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August",
          "September", "October", "November", "December"]


def field(path, pattern):
    m = re.search(pattern, open(path, encoding="utf-8").read(), re.M)
    if not m:
        sys.exit(f"FAIL {path}: no match for {pattern}")
    return m.group(1)


def main():
    pdf = None
    if sys.argv[1:2] == ["--pdf"] and len(sys.argv) == 3:
        pdf = sys.argv[2]
    elif len(sys.argv) > 1:
        sys.exit("usage: check-version.py [--pdf FILE]")
    version = field("lakefile.toml", r'^version\s*=\s*"([^"]+)"')
    cff_version = field("CITATION.cff", r'^version:\s*"?([^"\s]+)"?\s*$')
    date = datetime.date.fromisoformat(field("CITATION.cff", r'^date-released:\s*"?([\d-]+)"?\s*$'))
    line = f"Draft v{version}, {date.day} {MONTHS[date.month - 1]} {date.year}"
    fails = []
    if cff_version != version:
        fails.append(f"CITATION.cff's version is {cff_version}, lakefile.toml's {version}")
    texts = {f: open(f, encoding="utf-8").read() for f in ("README.md", "blueprint/README.md")}
    if pdf:
        run = subprocess.run(["pdftotext", pdf, "-"], capture_output=True, text=True)
        if run.returncode != 0:
            fails.append(f"pdftotext failed on {pdf}: {run.stderr.strip()}")
        texts[pdf] = run.stdout
    for f, t in texts.items():
        if line not in " ".join(t.split()):
            fails.append(f"{f} does not say \"{line}\"")
    for x in fails:
        print("FAIL " + x)
    checked = ", ".join(["CITATION.cff"] + list(texts)) + ("" if pdf else " (the PDF not checked)")
    print(f"{line}: {checked}; {len(fails)} failures")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
