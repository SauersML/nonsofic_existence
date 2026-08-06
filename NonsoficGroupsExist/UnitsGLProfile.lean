import NonsoficGroupsExist.MainResults
import NonsoficGroupsExist.RefineLoopDischarge

/-!
# The full profile of the unit group and of every `GL_r`

Theorem B(i) of the manuscript, closed in Lean: over every finite field
`k`, the unit group `L_k(1,2)ˣ` — and with it every positive-rank
`GL_r(L_k(1,2))` — is finitely generated, infinite, Kazhdan, and
nonsofic.  The route is the manuscript's own: the unconditional
`glTwo_eq_elementary_holds` from the `K₁` chain collapses `GL₂` onto the
rank-two elementary group, the prefix-code units equivalence identifies
`Lˣ` with `GL₂`, and the four properties transport along the composite
isomorphism from the already-closed elementary profile.  Previously only
nonsoficity of these groups was assembled; the finite
generation, infinitude, and property-`(T)` components are new here.
-/

namespace NonsoficGroupsExist

open BinaryLeavitt

variable (k : Type) [Field k]

/-- `EL₂ = GL₂` over the binary Leavitt algebra, as a subgroup
equality: the rank-two elementary subgroup is everything. -/
theorem binaryLeavitt_elementaryGroup_two_eq_top :
    elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) = ⊤ := by
  ext M
  simp only [Subgroup.mem_top, iff_true]
  exact glTwo_eq_elementary_holds k M

/-- The unit group of `L_k(1,2)` is explicitly isomorphic to the
rank-two elementary group: the two-leaf prefix code identifies `Lˣ`
with `GL₂`, and `GL₂ = EL₂`. -/
noncomputable def binaryLeavittUnitsEquivEL :
    BinaryLeavittUnits k ≃* BinaryLeavittEL k 1 :=
  (((BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode 1)
      ((BinaryLeavitt.family k).leftCombCode_complete 1)).symm.trans
    Subgroup.topEquiv.symm).trans
    (MulEquiv.subgroupCongr
      (binaryLeavitt_elementaryGroup_two_eq_top k).symm)

/-- **Theorem B(i) of the manuscript, closed**: over every finite field
`k`, the unit group `L_k(1,2)ˣ` is finitely generated, infinite, has
Kazhdan's property `(T)`, and is not sofic. -/
theorem binaryLeavittUnits_profile [Finite k] :
    Group.FG (BinaryLeavittUnits k) ∧
      Infinite (BinaryLeavittUnits k) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittUnits k) ∧
      ¬ IsSofic (BinaryLeavittUnits k) := by
  obtain ⟨hfg, hinf, hT, hns⟩ :=
    binaryLeavitt_finiteField_profile k 1 le_rfl
  let e : BinaryLeavittUnits k ≃* BinaryLeavittEL k 1 :=
    binaryLeavittUnitsEquivEL k
  haveI := hfg
  haveI := hinf
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Group.fg_of_surjective (f := e.symm.toMonoidHom)
      e.symm.surjective
  · exact Infinite.of_injective (e.symm : BinaryLeavittEL k 1 →
      BinaryLeavittUnits k) e.symm.injective
  · exact HasKazhdanPropertyT.of_mulEquiv e hT
  · intro h
    exact hns ((isSofic_mulEquiv_iff e).mp h)

/-- **Theorem B for every positive-rank general linear group, closed**:
over every finite field `k` and for every `m`, the group
`GL_{m+1}(L_k(1,2))` is finitely generated, infinite, has Kazhdan's
property `(T)`, and is not sofic. -/
theorem binaryLeavittGL_profile [Finite k] (m : ℕ) :
    Group.FG (BinaryLeavittGL k m) ∧
      Infinite (BinaryLeavittGL k m) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittGL k m) ∧
      ¬ IsSofic (BinaryLeavittGL k m) := by
  obtain ⟨hfg, hinf, hT, hns⟩ := binaryLeavittUnits_profile k
  let e : BinaryLeavittGL k m ≃* BinaryLeavittUnits k :=
    (BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode m)
      ((BinaryLeavitt.family k).leftCombCode_complete m)
  haveI := hfg
  haveI := hinf
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Group.fg_of_surjective (f := e.symm.toMonoidHom)
      e.symm.surjective
  · exact Infinite.of_injective (e.symm : BinaryLeavittUnits k →
      BinaryLeavittGL k m) e.symm.injective
  · exact HasKazhdanPropertyT.of_mulEquiv e hT
  · intro h
    exact hns ((isSofic_mulEquiv_iff e).mp h)

end NonsoficGroupsExist
