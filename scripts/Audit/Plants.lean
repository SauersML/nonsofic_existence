import Lean

/-!
# Planted defects, for calibrating the scans

gnomon runs a calibration before every detector whose verdict it reads, and
states the reason in each CI step: a detector that reports nothing is
indistinguishable from a clean corpus, so its silence is not evidence until
both directions are asserted.  Its laundering, identity-gate, round-trip,
metamorphic and correspondence guards each have one of these.

This is that corpus for `Audit.Scan`.  Every declaration below is either a
defect that a named scan must report, or a clean declaration that no scan may
report -- and the second half is not decoration.  It is what fails when a scan
stops distinguishing and starts alarming at everything, which is the failure
mode a zero-tolerance gate quietly rewards.

`scripts/Calibrate.lean` asserts both directions, and CI runs it BEFORE the
real audit.  This module is deliberately Mathlib-free, so the calibration
holds even when the corpus does not build.
-/

namespace AuditPlant

/-! ## Defects.  Each must be reported, under the tag named in its comment. -/

/-- AXIOM: a hand-declared axiom in the corpus. -/
axiom plantedAxiom : True

/-- TAUTOLOGY: the conclusion is the premise, under a name claiming the
conclusion.  Note that its `#print axioms` is perfectly clean, which is why the
axiom scan cannot see it. -/
theorem plantedTautology (h : 0 = 0) : 0 = 0 := h

/-- UNCONDITIONAL: the name promises existence; the type still takes a
premise. -/
theorem plantedExistsUnderPremise (h : (0 : Nat) = 0) : ∃ n : Nat, n = 0 :=
  ⟨0, h⟩

/-- INSTANCE_PREMISE: a Prop premise in implicit syntax, invisible to a reader
skimming the signature. -/
theorem plantedHiddenPremise {h : (0 : Nat) = 0} : (0 : Nat) = 0 ∧ True :=
  ⟨h, trivial⟩

/-- EMPTY_PREMISE: vacuously true, and provable for the same reason whatever
the conclusion says. -/
theorem plantedVacuous (h : False) : (0 : Nat) = 1 := h.elim

/-- TRIVIAL + UNUSED: concludes `True`, and its premise occurs in neither the
rest of the type nor the proof term.

The linter is disabled for this declaration alone, and `h` deliberately keeps
its leading-underscore-free name: the underscore is exactly the admission the
UNUSED scan accepts (`Audit.Scan.deliberate`), so a plant that spelled it `_h`
would no longer be the defect it exists to plant.  Renaming the binder or
widening this `set_option` past the one declaration silently decalibrates the
UNUSED scan. -/
set_option linter.unusedVariables false in
theorem plantedUnusedHypothesis (h : (0 : Nat) = 0) : True := trivial

/-- DUPLICATE + RFL. -/
theorem plantedDuplicateA : (1 : Nat) + 1 = 2 := rfl

/-- DUPLICATE + RFL: the same proposition under a second name. -/
theorem plantedDuplicateB : (1 : Nat) + 1 = 2 := rfl

/-- LAUNDERED_PROP: a named proposition nothing is ever proved to satisfy. -/
def PlantedLaunderedProp (n : Nat) : Prop := n = n + 1

/-- UNWITNESSED: Prop-valued fields, and no closed term of it anywhere. -/
structure PlantedCertificate where
  bound : Nat
  law : bound = bound + 1

/-- The axiom traversal must descend through PROOF TERMS, not merely notice
declarations that are themselves axioms.  This theorem's type mentions no
axiom; only its proof reaches `Classical.choice`.  Asserted directly in
`scripts/Calibrate.lean`, because the plain axiom plant above passes even when
the descent is completely broken. -/
theorem plantedReachesClassical (p : Prop) (h : ¬¬p) : p :=
  Classical.byContradiction h

/-! ### False-positive guards for the establishment criterion

Each of these is a defect the scans REPORTED on the real corpus and should
not have.  They are plants in the opposite direction: the scan must stay
silent about them. -/

/-- Stands in for Mathlib's `Finite`, which is a Prop-valued class.  A theorem
stated for such a class is naming the category it works in, not assuming its
inhabitants into existence. -/
class PlantedStructuralClass (α : Type) : Prop where
  ok : True

instance : PlantedStructuralClass Nat := ⟨trivial⟩

def EstablishedUnderStructuralClass (α : Type) : Prop := α = α

/-- Must NOT be LAUNDERED_PROP.  This is the shape of `isLEF_of_finite`, and
the first version of the criterion reported the proposition it establishes as
never established. -/
theorem establishedUnderStructuralClass (α : Type) [PlantedStructuralClass α] :
    EstablishedUnderStructuralClass α := rfl

def OnlyEstablishedConditionally (α : Type) : Prop := α = α

/-- Must STILL be LAUNDERED_PROP: an explicit Prop premise really does
relocate the obligation, and widening the criterion must not lose that. -/
theorem onlyEstablishedConditionally (α : Type) (h : α = α) :
    OnlyEstablishedConditionally α := h

/-- Must NOT be UNWITNESSED: constructed inside a proof term while the
conclusion is about something else, which is exactly how `isSofic_of_fintype`
constructs a `SoficModel`. -/
structure PlantedInnerCertificate where
  bound : Nat
  law : bound = bound

def plantedInnerCertificateUser : Nat :=
  (⟨0, rfl⟩ : PlantedInnerCertificate).bound

/-- Must be UNCONDITIONAL: a headline claim word, at the root of the corpus
namespace, on a type that still takes a premise. -/
theorem plantedNonsoficUnconditional (h : (0 : Nat) = 0) : ∃ n : Nat, n = 0 :=
  ⟨0, h⟩

/-- Must be ASSUMPTION_INSTANCE: an assumption written in instance syntax. -/
theorem plantedNonemptyAssumption [Nonempty Nat] : True := trivial

/-- Must NOT be RFL: a `@[simp]` lemma proved by `rfl` is a deliberate API
lemma, which is what 96 of the corpus's 96 hits were. -/
@[simp] theorem plantedSimpRfl : (2 : Nat) + 0 = 2 := rfl

/-! ## Clean declarations.  No scan may report any of these. -/

/-- Not LAUNDERED_PROP: established below. -/
def CleanProp (n : Nat) : Prop := n = n

theorem cleanProp_holds (n : Nat) : CleanProp n := rfl

/-- Not UNWITNESSED: a closed term of it is exhibited below. -/
structure CleanCertificate where
  bound : Nat
  law : bound = bound

def cleanCertificate : CleanCertificate := ⟨0, rfl⟩

/-- Not UNUSED: Lean's own convention for a deliberately unused binder is the
leading underscore, which its `unusedVariables` linter respects.  Honouring it
keeps the scan silent without an allow-list, and makes the underscore
an admission a reader can grep for rather than a way around the check. -/
theorem cleanDeliberateUnused (_h : (0 : Nat) = 0) : (1 : Nat) ≤ 1 :=
  Nat.le_refl 1

/-- Not TAUTOLOGY: the conclusion genuinely uses the premise without being
it. -/
theorem cleanUsesPremise (h : (0 : Nat) = 0) : (0 : Nat) = 0 ∧ (1 : Nat) = 1 :=
  ⟨h, rfl⟩

end AuditPlant
