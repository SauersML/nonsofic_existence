import Superseded.BlockMoveTailKill
import Superseded.DiagonalDescent
import Superseded.GammaDischarge
import Superseded.GammaReduction
import Superseded.KillMoves
import Superseded.MasterInduction
import Superseded.NarrowDischarge
import Superseded.NonnegUnitStructure
import Superseded.RankOneNormalForm
import Superseded.TailSupportReduction
import Superseded.TriangularFactorization
import Superseded.WindowDichotomy

/-!
# Superseded developments

Structure theory that a later, shorter route made unnecessary.  Nothing in
`NonsoficGroupsExist` imports any of it, and the library root does not import
this module, so none of it reaches the kernel audit: `scripts/Audit.lean`
walks the environment of the library root, and these declarations are not in
it.  That separation is the point -- this code is explicitly off the trust
surface, and saying so in a directory name is more honest than leaving it
where a reader would assume it carries weight.

It is still built by CI, so it cannot quietly rot into something that no
longer compiles, and `scripts/check.py` still scans it for every forbidden
construct it scans the live library for.  Superseded is not the same as
unchecked.

What is here, and what replaced it:

* `TriangularFactorization` -- an early factorization route, superseded by the
  pencil elimination of `RefineLoopDischarge`.
* `GammaReduction`, `GammaDischarge` -- the gamma-invariant discharge,
  superseded by the two-exit loop, which needs no termination measure.
* `RankOneNormalForm`, `WindowDichotomy`, `KillMoves`, `BlockMoveTailKill`,
  `NonnegUnitStructure`, `TailSupportReduction`, `DiagonalDescent` -- the
  master-induction extraction pipeline.  The refine loop discharges the same
  obligations with no extraction and no peeling step; these remain as
  standalone structure theory.
-/
