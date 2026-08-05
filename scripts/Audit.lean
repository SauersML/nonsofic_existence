import NonsoficGroupsExist
import Audit.Scan
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel audit of the headline theorems

`lake build` establishes that every module elaborates.  It does **not**
establish what the resulting proof terms depend on: a `sorry` anywhere in the
library elaborates fine and only shows up as the `sorryAx` axiom in the closure
of whatever used it, and `native_decide` shows up as `Lean.ofReduceBool`.

This file is run by CI with `lake env lean scripts/Audit.lean` after the build.
It fails, with a nonzero exit code, if either check below fails:

1. **Statement pinning.**  The `example`s restate the headline theorems
   verbatim.  If a statement is ever weakened or has a premise added, the
   corresponding `example` stops typechecking.
2. **Transitive axiom closure.**  Every declaration in the
   `NonsoficGroupsExist` namespace is traversed through the *kernel*
   environment, and the accumulated axiom set must be contained in the three
   axioms of classical Lean.  `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler` and any hand-declared `axiom` are all rejected here.
-/

open Lean Elab Command

namespace NonsoficGroupsExist.Audit

/-! ## 1. Statement pinning -/

example : ∃ (G : Type) (_ : Group G), ¬ IsSofic G :=
  nonsofic_groups_exist

example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ ¬ IsSofic G :=
  exists_finitelyPresented_nonsofic_group

example : ¬ IsSofic UniversalRankFour.Ambient :=
  universalLeavittEL4_not_isSofic

example : ¬ IsSofic UniversalRankFour.Core :=
  universalLeavittEL3_not_isSofic

example : ¬ IsSofic UniversalLeavittUnits :=
  universalLeavittUnits_not_isSofic

example (m : ℕ) : ¬ IsSofic (UniversalLeavittGL m) :=
  universalLeavittGL_not_isSofic m

example (k : Type) [Field k] [Finite k] :
    ¬ IsSofic (BinaryLeavittUnits k) :=
  binaryLeavittUnits_not_isSofic k

example (k : Type) [Field k] [Finite k] (m : ℕ) :
    ¬ IsSofic (BinaryLeavittGL k m) :=
  binaryLeavittGL_not_isSofic k m

example : ¬ IsLEF ↥ThompsonV.thompsonV :=
  BinaryLeavitt.thompsonV_not_isLEF

example (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) :=
  universalLeavitt_profile m hm

example (k : Type) [Field k] [Finite k]
    (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (BinaryLeavittEL k m) ∧
      Infinite (BinaryLeavittEL k m) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) ∧
      ¬ IsSofic (BinaryLeavittEL k m) :=
  binaryLeavitt_finiteField_profile k m hm

example :
    Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient :=
  ambient_profile

example :
    Countable UniversalRankFour.Ambient ∧
      Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient :=
  ambient_full_profile

example :
    ∃ (H : Type) (_ : Group H),
      Infinite H ∧ Group.IsFinitelyPresented H ∧ ¬ IsSofic H ∧
        ∃ π : H →* UniversalRankFour.Ambient,
          Function.Surjective π :=
  exists_infinite_finitelyPresented_nonsofic_ambient_cover

/-- The positive control, pinned here so that it cannot be deleted while the
negative results remain.  Every other occurrence of `IsSofic` in the library is
a hypothesis to refute or a conclusion under a `¬`; if no group is ever
exhibited satisfying it, `¬ IsSofic G` is equally consistent with the
definition being unsatisfiable, and a kernel-clean proof of it would be worth
nothing.  See `NonsoficGroupsExist/SoficPositiveControl.lean`. -/
example (G : Type) [Group G] [Fintype G] [DecidableEq G] : IsSofic G :=
  isSofic_of_fintype G

example (G : Type) [Group G] [Finite G] : IsSofic G :=
  isSofic_of_finite G

example : IsSofic (Multiplicative ℤ) :=
  isSofic_multiplicative_int

example (G : Type) [Group G] :
    IsSofic G ↔ IsSoficProductRestricted G :=
  isSofic_iff_productRestricted G

example (G : Type) [Group G] [Finite G] : IsLEF G :=
  isLEF_of_finite G

example : IsLEF (Multiplicative ℤ) :=
  isLEF_multiplicative_int

example (G : Type) [Group G] [Finite G] : IsTextbookLEF G :=
  isTextbookLEF_of_finite G

example : IsTextbookLEF (Multiplicative ℤ) :=
  isTextbookLEF_multiplicative_int

example (G : Type) [Group G] : IsLEF G ↔ IsTextbookLEF G :=
  isLEF_iff_textbook G

example {H : Type} [Group H] [Finite H]
    (f : FreeGroup (Fin 2) →* H)
    (h₁ : f ThompsonFObstruction.relator₁ = 1)
    (h₂ : f ThompsonFObstruction.relator₂ = 1) :
    f ThompsonFObstruction.generatorCommutator = 1 :=
  ThompsonFObstruction.finite_image_generatorCommutator_eq_one f h₁ h₂

/-! ## 2. Transitive axiom closure -/

/-- The axioms of classical Lean, which Mathlib itself uses.  Nothing else is
permitted anywhere in this development.

`lcProof` is deliberately absent: it is the compiler's erased-proof placeholder
and reaches a kernel closure through `partial def` and friends.  This library
has none, so if it ever appears the right response is to find out which
declaration introduced it, not to widen this list. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The public results.  Their individual closures are reported separately so
that a CI log records exactly what each headline theorem rests on. -/
def headlineTheorems : List Name :=
  [``nonsofic_groups_exist,
   ``exists_finitelyPresented_nonsofic_group,
   ``exists_infinite_finitelyPresented_nonsofic_ambient_cover,
   ``universalLeavittEL4_not_isSofic,
   ``universalLeavittEL3_not_isSofic,
   ``universalLeavittUnits_not_isSofic,
   ``universalLeavittGL_not_isSofic,
   ``binaryLeavittUnits_not_isSofic,
   ``binaryLeavittGL_not_isSofic,
   ``BinaryLeavitt.thompsonV_not_isLEF,
   ``universalLeavitt_profile,
   ``binaryLeavitt_finiteField_profile,
   ``ambient_profile,
   ``ambient_full_profile]

/-- Every declaration of this development, taken from the environment rather
than from a hand-maintained list, so that a new module cannot escape the
audit by not being mentioned here. -/
def projectDeclarations (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if (`NonsoficGroupsExist).isPrefixOf n then acc.push n else acc

/-- The union of the transitive axiom closures of `roots`. -/
def axiomClosure (roots : Array Name) : CommandElabM (Array Name) := do
  let mut result := #[]
  for n in roots do
    let axioms ← collectAxioms n
    for a in axioms do
      unless result.contains a do
        result := result.push a
  return result

def disallowed (axioms : Array Name) : Array Name :=
  axioms.filter fun a => !allowedAxioms.contains a

run_cmd do
  let env ← getEnv

  for n in headlineTheorems do
    unless env.contains n do
      throwError "audit target `{n}` does not exist in the environment"
    let axioms ← collectAxioms n
    let bad := disallowed axioms
    unless bad.isEmpty do
      throwError "`{n}` depends on disallowed axioms: {bad.toList}"
    logInfo m!"{n} depends on: {axioms.toList}"

  let decls := projectDeclarations env
  if decls.size < 100 then
    throwError "only {decls.size} declarations found in the `NonsoficGroupsExist` \
namespace; the audit is not seeing the library"
  let axioms ← axiomClosure decls
  let bad := disallowed axioms
  unless bad.isEmpty do
    throwError "the `NonsoficGroupsExist` namespace depends on disallowed \
axioms: {bad.toList}"
  logInfo m!"audited {decls.size} declarations; no disallowed axioms"

/-! ## 3. The environment scans

`Audit.Scan` carries the detectors and `scripts/Calibrate.lean` proves they can
fire; this section runs them on the real corpus and decides the exit code.

**The budget is the gate, and it lives here rather than in a JSON file** so
that raising one is a diff a reviewer sees.  `some 0` is a hard zero.  `none`
is report-only: the count is printed but does not fail the run, which is the
honest state for a scan whose baseline on this corpus has never been measured.
Replace a `none` with the measured count once CI has printed it and the tag
becomes a ratchet that can only go down.  A tag that produces findings but has
no row here is an error rather than a silent drop, so a scan cannot be disabled
by deleting its budget. -/

def budgets : List (String × Option Nat) :=
  [ ("AXIOM", some 0)            -- anything here is a trust bypass
  , ("TAUTOLOGY", some 0)        -- a proof that is its own premise is never intended
  , ("EMPTY_PREMISE", some 0)    -- a vacuously true theorem is never intended
  , ("UNCONDITIONAL", some 0)
  , ("LAUNDERED_PROP", some 0)
  , ("UNWITNESSED", some 0)
  -- Audited structural `[Nonempty ...]` inputs used to obtain positive finite
  -- cardinalities or select an index.  This is a ratchet, not report-only.
  , ("ASSUMPTION_INSTANCE", some 28)
  , ("UNUSED", some 0)
  , ("TRIVIAL", some 0)
  , ("DUPLICATE", some 0)
  , ("RFL", some 0) ]

/-- Keep this above every ratcheted budget so a failing log names all hits. -/
def examplesPerTag : Nat := 64

run_cmd do
  let env ← getEnv
  let findings ← liftTermElabM <|
    Audit.allScans env `NonsoficGroupsExist allowedAxioms

  let mut failures : Array String := #[]
  let mut covered : Array String := #[]

  for (tag, budget) in budgets do
    covered := covered.push tag
    let hits := findings.filter (fun f => f.tag == tag)
    let examples := (hits.map (·.decl)).toList.take examplesPerTag
    match budget with
    | some b =>
        if hits.size > b then
          failures := failures.push
            s!"{tag}: {hits.size} findings, budget {b}; e.g. {examples}"
        else
          logInfo m!"{tag}: {hits.size} (budget {b})"
    | none =>
        logInfo m!"{tag}: {hits.size} (report-only) {examples}"

  -- Once per tag, not once per finding: a renamed tag produced one line of
  -- signal and 255 lines of repetition the first time this fired.
  let mut orphanTags : Array String := #[]
  for f in findings do
    unless covered.contains f.tag || orphanTags.contains f.tag do
      orphanTags := orphanTags.push f.tag
      failures := failures.push
        s!"{f.tag}: produced findings but has no budget row (a scan cannot be \
disabled by deleting its budget, and a renamed tag must be renamed here too)"

  unless failures.isEmpty do
    throwError "audit failed:{Format.line}{Format.joinSep failures.toList Format.line}"

end NonsoficGroupsExist.Audit
