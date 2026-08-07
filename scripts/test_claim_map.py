#!/usr/bin/env python3
"""Regression tests for the claim-map parser and resolver.

Each test is a shape that once failed silently or that the resolver must
reject loudly: nested braces in notes (the lazy-regex truncation), pipes in
Markdown cells, multi-line note blocks, suffix-qualified names, within-file
ambiguity, and same-basename modules in different directories.  Run directly:

    python3 scripts/test_claim_map.py

CI runs it wherever `scripts/check.py` runs; a parser that silently drops or
truncates a note is exactly the failure a generated table exists to prevent.
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import claim_map


def _claims(tex: str) -> list:
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "t.tex"
        p.write_text(tex, encoding="utf-8")
        return claim_map.read_claims(p)


TEX_HEAD = "\\begin{theorem}\\label{thm:x}%\n"
TEX_TAIL = "\nBody.\n\\end{theorem}\n"


class ParseNote(unittest.TestCase):
    def test_nested_braces_survive(self):
        # The exact shape that used to truncate: math with nested TeX groups.
        tex = (TEX_HEAD
               + "\\leanverified{\\leanmod{M/A}{d1}\\leannote{the divergence "
                 "$\\abs{D_{n,i(n)}}\\to\\infty$; \\texttt{d_1} carries it.}}%"
               + TEX_TAIL)
        (c,) = _claims(tex)
        self.assertIn("\\abs{D_{n,i(n)}}\\to\\infty", c.note)
        self.assertTrue(c.note.endswith("carries it."))

    def test_multiline_blocks_and_note(self):
        tex = (TEX_HEAD
               + "\\leanverified{\\leanmod{M/A}{d1,d2}\n"
                 "\\leanmod{M/B}{d3}\n"
                 "\\leannote{spans\nlines {with braces}.}}%"
               + TEX_TAIL)
        (c,) = _claims(tex)
        self.assertEqual(c.declarations,
                         [("M/A", "d1"), ("M/A", "d2"), ("M/B", "d3")])
        self.assertEqual(c.note, "spans lines {with braces}.")
        self.assertTrue(c.wrapped)

    def test_partial_status_and_trailing_note(self):
        tex = (TEX_HEAD
               + "\\leanpartial{\\leanmod{M/A}{d1}}{only half, "
                 "the rest {nested} is prose.}%"
               + TEX_TAIL)
        (c,) = _claims(tex)
        self.assertEqual(c.status, "partial")
        self.assertEqual(c.note, "only half, the rest {nested} is prose.")

    def test_pipes_escaped_in_markdown(self):
        tex = (TEX_HEAD
               + "\\leanverified{\\leanmod{M/A}{d1}\\leannote{a $|x|$ bound.}}%"
               + TEX_TAIL)
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "t.tex").write_text(tex, encoding="utf-8")
            md = claim_map.to_markdown(_claims(tex), root)
        row = next(line for line in md.splitlines() if "thm:x" in line)
        self.assertIn("\\|x\\|", row)
        # The row still has exactly the four columns.
        self.assertEqual(row.count("|") - row.count("\\|"), 5)


def _tree(files: dict[str, str]) -> tempfile.TemporaryDirectory:
    d = tempfile.TemporaryDirectory()
    root = Path(d.name)
    for rel, text in files.items():
        p = root / claim_map.LIB / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    return d


def _resolve(files: dict[str, str], tex_body: str) -> list[str]:
    d = _tree(files)
    root = Path(d.name)
    (root / claim_map.TEX_NAME).write_text(tex_body, encoding="utf-8")
    claims = claim_map.read_claims(root / claim_map.TEX_NAME)
    try:
        _, problems = claim_map.resolve(claims, root)
    finally:
        d.cleanup()
    return problems


LEAN_TWO_NAMESPACES = """namespace NonsoficGroupsExist
namespace One
theorem dup : True := trivial
end One
namespace Two
theorem dup : True := trivial
end Two
end NonsoficGroupsExist
"""


class Resolve(unittest.TestCase):
    def test_suffix_qualification_resolves_ambiguity(self):
        tex = (TEX_HEAD
               + "\\leanverified{\\leanmod{A}{One.dup,Two.dup}}%"
               + TEX_TAIL)
        self.assertEqual(_resolve({"A.lean": LEAN_TWO_NAMESPACES}, tex), [])

    def test_bare_ambiguous_name_is_an_error(self):
        tex = TEX_HEAD + "\\leanverified{\\leanmod{A}{dup}}%" + TEX_TAIL
        problems = _resolve({"A.lean": LEAN_TWO_NAMESPACES}, tex)
        self.assertEqual(len(problems), 1)
        self.assertIn("ambiguous", problems[0])

    def test_same_stem_modules_do_not_pool_declarations(self):
        # `B/A.lean` declaring `only_in_b` must not let a note pointing at the
        # top-level `A` module claim it.
        files = {
            "A.lean": "namespace NonsoficGroupsExist\ntheorem in_a : True := trivial\nend NonsoficGroupsExist\n",
            "B/A.lean": "namespace NonsoficGroupsExist\ntheorem only_in_b : True := trivial\nend NonsoficGroupsExist\n",
        }
        tex = TEX_HEAD + "\\leanverified{\\leanmod{A}{only_in_b}}%" + TEX_TAIL
        problems = _resolve(files, tex)
        self.assertEqual(len(problems), 1)
        self.assertIn("does not declare", problems[0])

    def test_noncomputable_section_keeps_namespace(self):
        # A bare `end` closing a `noncomputable section` must not pop the
        # namespace; the declaration after it keeps its full prefix.
        lean = ("namespace NonsoficGroupsExist\n"
                "namespace Deep\n"
                "noncomputable section\n"
                "theorem inside : True := trivial\n"
                "end\n"
                "end Deep\n"
                "theorem after : True := trivial\n"
                "end NonsoficGroupsExist\n")
        d = _tree({"A.lean": lean})
        try:
            import lean_decls
            index = lean_decls.build_index(Path(d.name))
            self.assertIn("NonsoficGroupsExist.Deep.inside", index)
            self.assertIn("NonsoficGroupsExist.after", index)
        finally:
            d.cleanup()

    def test_dangling_reference_is_an_error(self):
        files = {"A.lean": "namespace NonsoficGroupsExist\ntheorem real : True := trivial\nend NonsoficGroupsExist\n"}
        tex = TEX_HEAD + "\\leanverified{\\leanmod{A}{ghost}}%" + TEX_TAIL
        problems = _resolve(files, tex)
        self.assertEqual(len(problems), 1)
        self.assertIn("ghost", problems[0])


if __name__ == "__main__":
    unittest.main(verbosity=1)
