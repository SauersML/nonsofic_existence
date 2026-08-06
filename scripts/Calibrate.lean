import Audit.Scan
import Audit.Plants

/-!
# Calibration of the environment scans, in both directions

Run by CI BEFORE the audit whose verdict it licenses:

    lake env lean scripts/Calibrate.lean

Direction 1: every planted defect in `Audit.Plants` is reported, under the tag
that names it.  The tag matters -- a gate that fires under the wrong label can
alarm but cannot localize.

Direction 2: every clean declaration is reported by nothing.  Without this half
a scan that had degenerated into reporting everything would pass direction 1
perfectly, and a zero-tolerance gate quietly rewards exactly that
degeneration -- the cheapest way to make a scan stop failing is to make it stop
distinguishing.

This file needs no Mathlib and no corpus, so the calibration still runs when
the library does not build -- which is when a broken detector is most likely to
be blamed on the corpus.
-/

open Lean Elab Command Audit

namespace AuditCalibrate

/-- Defects, and the tag each must be reported under. -/
def mustReport : List (String × Name) :=
  [("AXIOM", ``AuditPlant.plantedAxiom),
   ("TAUTOLOGY", ``AuditPlant.plantedTautology),
   ("UNCONDITIONAL", ``AuditPlant.plantedNonsoficUnconditional),
   ("ASSUMPTION_INSTANCE", ``AuditPlant.plantedNonemptyAssumption),
   ("LAUNDERED_PROP", ``AuditPlant.OnlyEstablishedConditionally),
   ("EMPTY_PREMISE", ``AuditPlant.plantedVacuous),
   ("TRIVIAL", ``AuditPlant.plantedUnusedHypothesis),
   ("UNUSED", ``AuditPlant.plantedUnusedHypothesis),
   ("LAUNDERED_PROP", ``AuditPlant.PlantedLaunderedProp),
   ("UNWITNESSED", ``AuditPlant.PlantedCertificate),
   ("STALE_DISCLAIMER", ``AuditPlant.plantedStaleDisclaimer)]

/-- Defects where either member of a pair may carry the finding, since which
one is reported depends on the order the environment is walked in. -/
def mustReportOneOf : List (String × List Name) :=
  [("DUPLICATE", [``AuditPlant.plantedDuplicateA, ``AuditPlant.plantedDuplicateB]),
   ("RFL", [``AuditPlant.plantedDuplicateA, ``AuditPlant.plantedDuplicateB])]

/-- Findings the scans must NOT produce: one row per false positive that the
first run against the real corpus actually emitted.  A detector is not fixed
because the number went down; it is fixed when the shape that was
misclassified is pinned here. -/
def mustNotReportUnder : List (String × Name) :=
  [-- `Finite` is a Prop-valued class, so the theorem that ESTABLISHES a
   -- proposition looked conditional and the proposition looked laundered.
   ("LAUNDERED_PROP", ``AuditPlant.EstablishedUnderStructuralClass),
   -- constructed inside a proof term, not in the conclusion
   ("UNWITNESSED", ``AuditPlant.PlantedInnerCertificate),
   -- `exists_foo_of_bar` is Lean's convention for a CONDITIONAL lemma
   ("UNCONDITIONAL", ``AuditPlant.plantedExistsUnderPremise),
   -- an ordinary implicit side condition is not an assumption in disguise
   ("ASSUMPTION_INSTANCE", ``AuditPlant.plantedHiddenPremise),
   -- a `@[simp]` lemma proved by `rfl` is a deliberate API lemma
   ("RFL", ``AuditPlant.plantedSimpRfl),
   -- prose calling a result conditional, on a type that names the condition
   ("STALE_DISCLAIMER", ``AuditPlant.cleanConditionalOnItsPremise)]

/-- Declarations no scan may report. -/
def mustNotReport : List Name :=
  [``AuditPlant.CleanProp,
   ``AuditPlant.CleanCertificate,
   ``AuditPlant.cleanDeliberateUnused,
   ``AuditPlant.cleanUsesPremise]

run_cmd do
  let env ← getEnv
  let findings ← liftTermElabM <|
    Audit.allScans env `AuditPlant [``propext, ``Classical.choice, ``Quot.sound]

  let mut failures : Array String := #[]

  for (tag, decl) in mustReport do
    unless findings.any (fun f ↦ f.tag == tag && f.decl == decl) do
      failures := failures.push
        s!"plant {decl} was NOT reported under {tag}"

  for (tag, decls) in mustReportOneOf do
    unless findings.any (fun f ↦ f.tag == tag && decls.contains f.decl) do
      failures := failures.push
        s!"no {tag} finding on any of {decls}"

  for (tag, decl) in mustNotReportUnder do
    if findings.any (fun f ↦ f.tag == tag && f.decl == decl) then
      failures := failures.push
        s!"false positive: {decl} reported under {tag}"

  for decl in mustNotReport do
    let hits := findings.filter (fun f ↦ f.decl == decl)
    unless hits.isEmpty do
      failures := failures.push
        s!"clean declaration {decl} was reported under {(hits.map (·.tag)).toList}"

  -- The claim-word test must read the LAST COMPONENT, not the full name.
  -- A corpus named after its own headline claim (this one is called
  -- `NonsoficGroupsExist`) otherwise matches every declaration in it, and the
  -- resulting 99 findings look like a working gate rather than a bug.
  unless Audit.promisesClaim `NonsoficGroupsExist.unconditional_existence do
    failures := failures.push "promisesClaim misses a genuine headline claim"
  if Audit.promisesClaim `NonsoficGroupsExist.mul_mem_tableDomain then
    failures := failures.push
      "promisesClaim matches the NAMESPACE: every declaration in a corpus \
named after its claim is reported"
  if Audit.promisesClaim `NonsoficGroupsExist.Sub.unconditional_thing then
    failures := failures.push "promisesClaim fires outside the corpus root"

  -- The axiom traversal must descend through proof terms.  Asserted separately
  -- from the findings above: the AXIOM plant is itself an `axiom`, so it is
  -- reported even when the descent through proofs is entirely broken -- which
  -- is exactly the state this repository's scans were in on first contact with
  -- the real toolchain.
  let reach := Audit.axiomClosure env #[``AuditPlant.plantedReachesClassical]
  unless reach.contains ``Classical.choice do
    failures := failures.push
      s!"axiom traversal does not descend through proof terms: closure of \
plantedReachesClassical is {reach.toList}, missing Classical.choice"

  for f in findings do
    logInfo m!"[{f.tag}] {f.decl}: {f.detail}"

  unless failures.isEmpty do
    throwError "calibration failed:{Format.line}{Format.joinSep failures.toList Format.line}"

  logInfo m!"calibration: {mustReport.length + mustReportOneOf.length} planted defects all reported, \
{mustNotReportUnder.length} false-positive shapes all silent, \
{mustNotReport.length} clean declarations all silent"

end AuditCalibrate
