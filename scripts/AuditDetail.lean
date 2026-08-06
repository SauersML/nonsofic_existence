import NonsoficGroupsExist
import Audit.Scan
import Lean.Elab.Command

open Lean Meta Elab Command

namespace NonsoficGroupsExist.AuditDetail

def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let findings ← liftTermElabM <|
    Audit.allScans env `NonsoficGroupsExist allowedAxioms
  for f in findings do
    logInfo m!"{f.tag} | {f.decl} | {f.detail}"

end NonsoficGroupsExist.AuditDetail
