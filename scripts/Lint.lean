import NonsoficGroupsExist
import Batteries.Tactic.Lint

/-!
# Style and hygiene linters

Batteries' `#lint` over the whole library: unused arguments, `simp` lemmas
that do not apply, missing docstrings on public declarations, definitions that
should be theorems, and the rest of the standard roster.

This is deliberately NOT one of the gates.  `scripts/Audit.lean` and
`scripts/check.py` answer questions about soundness, and a soundness gate that
also fails on a missing docstring trains people to ignore it.  Run under
`lake env lean scripts/Lint.lean`.
-/

open Batteries.Tactic.Lint

#lint only unusedArguments defLemma dupNamespace simpNF simpVarHead
