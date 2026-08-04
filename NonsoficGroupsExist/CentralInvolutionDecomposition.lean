import NonsoficGroupsExist.KazhdanFixedSpace
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Simultaneous eigenspaces of finite central involutions

A finite central elementary abelian subgroup acts by a commuting family of
symmetric involutions in every finite-dimensional real orthogonal
representation.  This file builds the resulting joint eigenspaces and proves
that every nonzero joint eigenspace carries a genuine scalar `±1` action.
-/

namespace NonsoficGroupsExist

universe u v

namespace CentralInvolutionDecomposition

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear operator associated to an element of a subgroup. -/
def operator (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G) (c : C) :
    E →ₗ[ℝ] E :=
  (rho c.1).toLinearEquiv.toLinearMap

/-- The simultaneous eigenspace belonging to a function of putative
eigenvalues.  Empty or inconsistent choices simply give the bottom
subspace. -/
def jointEigenspace (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (chi : C → ℝ) : Submodule ℝ E :=
  ⨅ c : C, Module.End.eigenspace (operator rho C c) (chi c)

/-- An orthogonal involution is symmetric. -/
theorem operator_isSymmetric
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (c : C) :
    (operator rho C c).IsSymmetric := by
  intro x y
  have hsq : rho c.1 (rho c.1 y) = y := by
    calc
      rho c.1 (rho c.1 y) = rho (c.1 * c.1) y := by
        change (rho c.1 * rho c.1) y = rho (c.1 * c.1) y
        rw [← map_mul]
      _ = y := by rw [← pow_two, hexp c.1 c.2]; simp
  change inner ℝ (rho c.1 x) y = inner ℝ x (rho c.1 y)
  calc
    inner ℝ (rho c.1 x) y =
        inner ℝ (rho c.1 x) (rho c.1 (rho c.1 y)) := by rw [hsq]
    _ = inner ℝ x (rho c.1 y) := (rho c.1).inner_map_map _ _

/-- Operators coming from a central subgroup commute pairwise. -/
theorem operator_pairwise_commute
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hcentral : C ≤ Subgroup.center G) :
    Pairwise (Function.onFun Commute (operator rho C)) := by
  intro c d _
  change Commute (operator rho C c) (operator rho C d)
  rw [commute_iff_eq]
  ext z
  change rho c.1 (rho d.1 z) = rho d.1 (rho c.1 z)
  have hcd : c.1 * d.1 = d.1 * c.1 :=
    (Subgroup.mem_center_iff.mp (hcentral c.2) d.1).symm
  calc
    rho c.1 (rho d.1 z) = rho (c.1 * d.1) z := by
      change (rho c.1 * rho d.1) z = rho (c.1 * d.1) z
      rw [← map_mul]
    _ = rho (d.1 * c.1) z := by rw [hcd]
    _ = rho d.1 (rho c.1 z) := by
      change rho (d.1 * c.1) z = (rho d.1 * rho c.1) z
      rw [map_mul]

/-- The joint eigenspaces form an orthogonal internal direct sum in finite
dimensions. -/
theorem jointEigenspaces_isInternal [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) :
    DirectSum.IsInternal (jointEigenspace rho C) := by
  classical
  exact LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    (operator_isSymmetric rho C hexp)
    (operator_pairwise_commute rho C hcentral)

/-- The joint eigenspaces are pairwise orthogonal, without a finite-
dimensional assumption. -/
theorem jointEigenspaces_orthogonalFamily
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) :
    OrthogonalFamily ℝ (fun chi : C → ℝ ↦ jointEigenspace rho C chi)
      (fun chi ↦ (jointEigenspace rho C chi).subtypeₗᵢ) :=
  LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces
    (operator_isSymmetric rho C hexp)

/-- Centrality makes every joint eigenspace invariant under the full group
action. -/
theorem map_mem_jointEigenspace
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hcentral : C ≤ Subgroup.center G) (chi : C → ℝ)
    (g : G) {z : E} (hz : z ∈ jointEigenspace rho C chi) :
    rho g z ∈ jointEigenspace rho C chi := by
  rw [jointEigenspace, Submodule.mem_iInf] at hz ⊢
  intro c
  rw [Module.End.mem_eigenspace_iff]
  have hcz := Module.End.mem_eigenspace_iff.mp (hz c)
  change rho c.1 z = chi c • z at hcz
  change rho c.1 (rho g z) = chi c • rho g z
  have hcg : c.1 * g = g * c.1 :=
    (Subgroup.mem_center_iff.mp (hcentral c.2) g).symm
  calc
    rho c.1 (rho g z) = rho (c.1 * g) z := by
      change (rho c.1 * rho g) z = rho (c.1 * g) z
      rw [← map_mul]
    _ = rho (g * c.1) z := by rw [hcg]
    _ = rho g (rho c.1 z) := by
      change rho (g * c.1) z = (rho g * rho c.1) z
      rw [map_mul]
    _ = rho g (chi c • z) := by rw [hcz]
    _ = chi c • rho g z := by rw [map_smul]

/-- The ambient action restricted linearly to one joint eigenspace. -/
def restrictedLinearMap
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hcentral : C ≤ Subgroup.center G) (chi : C → ℝ) (g : G) :
    jointEigenspace rho C chi →ₗ[ℝ] jointEigenspace rho C chi where
  toFun z := ⟨rho g z.1, map_mem_jointEigenspace rho C hcentral chi g z.2⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp] theorem restrictedLinearMap_coe
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hcentral : C ≤ Subgroup.center G) (chi : C → ℝ) (g : G)
    (z : jointEigenspace rho C chi) :
    (restrictedLinearMap rho C hcentral chi g z : E) = rho g z.1 := rfl

/-- Recomposition intertwines the componentwise restricted action with the
ambient action. -/
theorem coeLinearMap_map_restricted
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G) (g : G)
    (d : DirectSum (C → ℝ) (fun chi ↦ jointEigenspace rho C chi)) :
    DirectSum.coeLinearMap (jointEigenspace rho C)
        (DirectSum.map (fun chi ↦
          (restrictedLinearMap rho C hcentral chi g).toAddMonoidHom) d) =
      rho g (DirectSum.coeLinearMap (jointEigenspace rho C) d) := by
  classical
  let lhs : DirectSum (C → ℝ) (fun chi ↦ jointEigenspace rho C chi) →+ E :=
    (DirectSum.coeLinearMap (jointEigenspace rho C)).toAddMonoidHom.comp
      (DirectSum.map (fun chi ↦
        (restrictedLinearMap rho C hcentral chi g).toAddMonoidHom))
  let rhs : DirectSum (C → ℝ) (fun chi ↦ jointEigenspace rho C chi) →+ E :=
    ((rho g).toLinearEquiv.toLinearMap.comp
      (DirectSum.coeLinearMap (jointEigenspace rho C))).toAddMonoidHom
  have heq : lhs = rhs := by
    apply DirectSum.addHom_ext
    intro chi z
    simp [lhs, rhs]
  exact DFunLike.congr_fun heq d

/-- The canonical finite-dimensional joint-eigenspace decomposition. -/
noncomputable def components [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (z : E) :
    DirectSum (C → ℝ) (fun chi ↦ jointEigenspace rho C chi) := by
  exact (LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (jointEigenspace rho C))
    (jointEigenspaces_isInternal rho C hcentral hexp)).symm z

theorem coeLinearMap_components [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (z : E) :
  DirectSum.coeLinearMap (jointEigenspace rho C)
      (components rho C hcentral hexp z) = z := by
  unfold components
  exact LinearEquiv.apply_ofBijective_symm_apply
    (DirectSum.coeLinearMap (jointEigenspace rho C))
    (h := jointEigenspaces_isInternal rho C hcentral hexp) z

/-- Joint-eigenspace components commute with the ambient group action. -/
theorem component_equivariant [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (g : G) (z : E) (chi : C → ℝ) :
    components rho C hcentral hexp (rho g z) chi =
      restrictedLinearMap rho C hcentral chi g
        (components rho C hcentral hexp z chi) := by
  let d := components rho C hcentral hexp z
  let d' := DirectSum.map (fun psi ↦
    (restrictedLinearMap rho C hcentral psi g).toAddMonoidHom) d
  have hcoe : DirectSum.coeLinearMap (jointEigenspace rho C) d' = rho g z := by
    calc
      DirectSum.coeLinearMap (jointEigenspace rho C) d' =
          rho g (DirectSum.coeLinearMap (jointEigenspace rho C) d) :=
        coeLinearMap_map_restricted rho C hcentral g d
      _ = rho g z := by rw [coeLinearMap_components rho C hcentral hexp z]
  have hd : d' = components rho C hcentral hexp (rho g z) := by
    apply (jointEigenspaces_isInternal rho C hcentral hexp).1
    change DirectSum.coeLinearMap (jointEigenspace rho C) d' =
      DirectSum.coeLinearMap (jointEigenspace rho C)
        (components rho C hcentral hexp (rho g z))
    rw [hcoe, coeLinearMap_components rho C hcentral hexp (rho g z)]
  have hcomponent := congrArg (fun e ↦ e chi) hd
  change restrictedLinearMap rho C hcentral chi g
      (components rho C hcentral hexp z chi) =
      components rho C hcentral hexp (rho g z) chi at hcomponent
  exact hcomponent.symm

/-- Components of a fixed vector remain fixed. -/
theorem component_fixed [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    [DecidableEq (C → ℝ)]
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) {g : G} {z : E}
    (hz : rho g z = z) (chi : C → ℝ) :
    restrictedLinearMap rho C hcentral chi g
        (components rho C hcentral hexp z chi) =
      components rho C hcentral hexp z chi := by
  rw [← component_equivariant rho C hcentral hexp g z chi, hz]

/-- Every eigenvalue occurring on a nonzero joint eigenspace of involutions
is `+1` or `-1`. -/
theorem jointEigenvalue_eq_one_or_neg_one
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (chi : C → ℝ)
    (hchi : jointEigenspace rho C chi ≠ ⊥) (c : C) :
    chi c = 1 ∨ chi c = -1 := by
  have hnontrivial : Nontrivial (jointEigenspace rho C chi) :=
    (jointEigenspace rho C chi).nontrivial_iff_ne_bot.mpr hchi
  obtain ⟨z, hz⟩ := exists_ne (0 : jointEigenspace rho C chi)
  have hz0 : (z : E) ≠ 0 := fun h ↦ hz (Subtype.ext h)
  have hzall : ∀ d : C,
      z.1 ∈ Module.End.eigenspace (operator rho C d) (chi d) := by
    simpa only [jointEigenspace, Submodule.mem_iInf] using z.2
  have heigen := Module.End.mem_eigenspace_iff.mp (hzall c)
  change rho c.1 z.1 = chi c • z.1 at heigen
  have hsq : rho c.1 (rho c.1 z.1) = z.1 := by
    calc
      rho c.1 (rho c.1 z.1) = rho (c.1 * c.1) z.1 := by
        change (rho c.1 * rho c.1) z.1 = rho (c.1 * c.1) z.1
        rw [← map_mul]
      _ = z.1 := by rw [← pow_two, hexp c.1 c.2]; simp
  have hcoef : chi c ^ 2 = 1 := by
    have hsmul : (chi c ^ 2 - 1) • z.1 = 0 := by
      rw [sub_smul, one_smul, pow_two, mul_smul, ← heigen,
        ← map_smul, ← heigen, hsq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hz0)
  rcases sq_eq_one_iff.mp hcoef with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- On a nonzero joint eigenspace, each central involution acts uniformly by
`+1` or uniformly by `-1`. -/
theorem action_eq_or_neg_on_jointEigenspace
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (C : Subgroup G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1) (chi : C → ℝ)
    (hchi : jointEigenspace rho C chi ≠ ⊥) (c : C) :
    (∀ z : jointEigenspace rho C chi, rho c.1 z.1 = z.1) ∨
      (∀ z : jointEigenspace rho C chi, rho c.1 z.1 = -z.1) := by
  have heigen (z : jointEigenspace rho C chi) :
      rho c.1 z.1 = chi c • z.1 := by
    have hzall : ∀ d : C,
        z.1 ∈ Module.End.eigenspace (operator rho C d) (chi d) := by
      simpa only [jointEigenspace, Submodule.mem_iInf] using z.2
    exact Module.End.mem_eigenspace_iff.mp (hzall c)
  rcases jointEigenvalue_eq_one_or_neg_one rho C hexp chi hchi c with h | h
  · left
    intro z
    rw [heigen z, h, one_smul]
  · right
    intro z
    rw [heigen z, h, neg_smul, one_smul]

end CentralInvolutionDecomposition
end NonsoficGroupsExist
