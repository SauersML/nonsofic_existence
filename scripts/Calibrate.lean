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
perfectly, and a budget-zero gate quietly rewards exactly that degeneration.

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
   ("UNCONDITIONAL", ``AuditPlant.plantedExistsUnderPremise),
   ("INSTANCE_PREMISE", ``AuditPlant.plantedHiddenPremise),
   ("EMPTY_PREMISE", ``AuditPlant.plantedVacuous),
   ("TRIVIAL", ``AuditPlant.plantedUnusedHypothesis),
   ("UNUSED", ``AuditPlant.plantedUnusedHypothesis),
   ("LAUNDERED_PROP", ``AuditPlant.PlantedLaunderedProp),
   ("UNWITNESSED", ``AuditPlant.PlantedCertificate)]

/-- Defects where either member of a pair may carry the finding, since which
one is reported depends on the order the environment is walked in. -/
def mustReportOneOf : List (String × List Name) :=
  [("DUPLICATE", [``AuditPlant.plantedDuplicateA, ``AuditPlant.plantedDuplicateB]),
   ("RFL", [``AuditPlant.plantedDuplicateA, ``AuditPlant.plantedDuplicateB])]

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

  for decl in mustNotReport do
    let hits := findings.filter (fun f ↦ f.decl == decl)
    unless hits.isEmpty do
      failures := failures.push
        s!"clean declaration {decl} was reported under {(hits.map (·.tag)).toList}"

  for f in findings do
    logInfo m!"[{f.tag}] {f.decl}: {f.detail}"

  unless failures.isEmpty do
    throwError "calibration failed:{Format.line}{Format.joinSep failures.toList Format.line}"

  logInfo m!"calibration: {mustReport.length + mustReportOneOf.length} planted defects all reported, \
{mustNotReport.length} clean declarations all silent"

end AuditCalibrate
