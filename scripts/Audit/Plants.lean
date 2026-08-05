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
mode a budget-zero gate quietly rewards.

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
rest of the type nor the proof term. -/
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
keeps the scan at budget zero without an allow-list, and makes the underscore
an admission a reader can grep for rather than a way around the check. -/
theorem cleanDeliberateUnused (_h : (0 : Nat) = 0) : (1 : Nat) ≤ 1 :=
  Nat.le_refl 1

/-- Not TAUTOLOGY: the conclusion genuinely uses the premise without being
it. -/
theorem cleanUsesPremise (h : (0 : Nat) = 0) : (0 : Nat) = 0 ∧ (1 : Nat) = 1 :=
  ⟨h, rfl⟩

end AuditPlant
