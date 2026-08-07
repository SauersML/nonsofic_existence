#!/usr/bin/env python3
"""Detect overlapping TikZ nodes in the manuscript's figures.

For every tikzpicture inside a figure environment of the manuscript, this
script compiles a standalone document that reproduces the picture with the
manuscript's class, fonts, and macros, appends a TikZ epilogue that writes
each named node's true bounding box (south west / north east anchors) to a
file, and then checks every pair of boxes for rectangle intersection.

Exit status is nonzero if any pair of nodes overlaps, so the script can run
as a CI gate.  Requires pdflatex on PATH.

Usage:  python3 scripts/check_fig_overlap.py [--tex nonsofic_groups_exist.tex]
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

# Two boxes whose borders merely kiss are fine; flag only real penetration.
TOLERANCE_PT = 0.5

PREAMBLE = r"""\documentclass[11pt]{amsart}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\IfFileExists{lmodern.sty}{\usepackage{lmodern}}{}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{tikz}
\usetikzlibrary{positioning,arrows.meta}
%% Cross-references resolve only in the full document; stand in a fixed
%% label of realistic width so text metrics match the real render.
\renewcommand{\ref}[1]{9.9}
\renewcommand{\eqref}[1]{(9.9)}
"""


def preamble_macros(source: str) -> str:
    """Single-line \newcommand definitions from the manuscript preamble."""
    preamble = source.split(r"\begin{document}")[0]
    lines = []
    for line in preamble.splitlines():
        stripped = line.strip()
        if re.match(r"\\(newcommand|DeclareMathOperator\*?"
                    r"|DeclarePairedDelimiter)\{\\[A-Za-z]+\}", stripped) \
                and stripped.count("{") == stripped.count("}") \
                and "lean" not in stripped:
            lines.append(stripped)
    return "\n".join(lines)


def extract_figures(source: str):
    """Yield (label, tikz_source) for each tikzpicture inside a figure."""
    for fig in re.finditer(
            r"\\begin\{figure\}.*?\\end\{figure\}", source, re.DOTALL):
        block = fig.group(0)
        label_m = re.search(r"\\label\{([^}]*)\}", block)
        tikz_m = re.search(
            r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", block, re.DOTALL)
        if tikz_m:
            yield (label_m.group(1) if label_m else "unlabeled",
                   tikz_m.group(0))


def node_names(tikz: str):
    return re.findall(r"\\node\s*(?:\[[^\]]*\])?\s*\(([^)]+)\)", tikz)


def bbox_epilogue(names) -> str:
    return (
        "\\makeatletter\n"
        "\\newwrite\\bboxfile\n"
        "\\immediate\\openout\\bboxfile=\\jobname.bboxes\n"
        "\\foreach \\bboxname in {" + ",".join(names) + "}{%\n"
        "  \\pgfpointanchor{\\bboxname}{south west}%\n"
        "  \\immediate\\write\\bboxfile{\\bboxname\\space sw"
        " \\the\\pgf@x\\space\\the\\pgf@y}%\n"
        "  \\pgfpointanchor{\\bboxname}{north east}%\n"
        "  \\immediate\\write\\bboxfile{\\bboxname\\space ne"
        " \\the\\pgf@x\\space\\the\\pgf@y}%\n"
        "}\n"
        "\\immediate\\closeout\\bboxfile\n"
        "\\makeatother\n"
    )


def read_bboxes(path: pathlib.Path):
    boxes = {}
    for line in path.read_text().splitlines():
        name, corner, x, y = line.split()
        entry = boxes.setdefault(name, {})
        entry[corner] = (float(x.rstrip("pt")), float(y.rstrip("pt")))
    return {
        name: (c["sw"][0], c["sw"][1], c["ne"][0], c["ne"][1])
        for name, c in boxes.items()
    }


def overlaps(a, b):
    dx = min(a[2], b[2]) - max(a[0], b[0])
    dy = min(a[3], b[3]) - max(a[1], b[1])
    if dx > TOLERANCE_PT and dy > TOLERANCE_PT:
        return dx, dy
    return None


def check_figure(label: str, tikz: str, macros: str, workdir: pathlib.Path,
                 dump: bool = False):
    names = node_names(tikz)
    if len(names) < 2:
        return []
    body = tikz.replace(
        "\\end{tikzpicture}", bbox_epilogue(names) + "\\end{tikzpicture}")
    jobname = re.sub(r"[^A-Za-z0-9]+", "-", label)
    tex = workdir / f"{jobname}.tex"
    tex.write_text(PREAMBLE + macros + "\n\\begin{document}\n"
                   + body + "\n\\end{document}\n")
    result = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=workdir, capture_output=True, text=True)
    bbox_path = workdir / f"{jobname}.bboxes"
    if result.returncode != 0 or not bbox_path.exists():
        tail = "\n".join(result.stdout.splitlines()[-25:])
        raise RuntimeError(f"{label}: standalone compile failed\n{tail}")
    boxes = read_bboxes(bbox_path)
    if dump:
        cm = 28.4528
        for name, (x0, y0, x1, y1) in sorted(boxes.items()):
            print(f"  {name:8s} x [{x0/cm:6.2f}, {x1/cm:6.2f}] "
                  f"y [{y0/cm:6.2f}, {y1/cm:6.2f}] cm")
    bad = []
    items = sorted(boxes.items())
    for i, (name_a, box_a) in enumerate(items):
        for name_b, box_b in items[i + 1:]:
            pen = overlaps(box_a, box_b)
            if pen:
                bad.append((name_a, name_b, pen))
    return bad


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", default="nonsofic_groups_exist.tex")
    parser.add_argument("--dump", action="store_true",
                        help="print every node's bounding box")
    args = parser.parse_args()
    source = pathlib.Path(args.tex).read_text()
    macros = preamble_macros(source)
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        for label, tikz in extract_figures(source):
            bad = check_figure(label, tikz, macros, pathlib.Path(tmp),
                               dump=args.dump)
            if bad:
                failures += len(bad)
                print(f"{label}: OVERLAP")
                for a, b, (dx, dy) in bad:
                    print(f"  {a} <-> {b}  penetration {dx:.1f}pt x {dy:.1f}pt")
            else:
                print(f"{label}: ok")
    if failures:
        print(f"\n{failures} overlapping node pair(s) found")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
