import NonsoficGroupsExist.Kazhdan
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Property `(T)` forces finite generation

A Kazhdan pair `(Q, ε)` leaves no room for a proper subgroup containing
`Q` of infinite index: the point mass at the trivial coset in the real
`ℓ²` space of the coset space is `Q`-fixed, so the pair produces a nonzero
invariant vector, which is a nonzero constant on a transitive orbit and
hence square-summable only over finitely many cosets.  A finite transversal
then augments `Q` to a finite generating set.  This discharges the
manuscript's repeated step “Kazhdan, hence finitely generated” without a
separate hypothesis.
-/

namespace NonsoficGroupsExist

namespace KazhdanFiniteGeneration

open scoped ENNReal InnerProductSpace

universe u

variable {α β : Type u}

/-- Coefficientwise reindexing of real `ℓ²` along an equivalence of index
types preserves square-summability. -/
theorem memℓp_comp_equiv (e : α ≃ β) (f : lp (fun _ : α ↦ ℝ) 2) :
    Memℓp (fun b : β ↦ f (e.symm b)) 2 := by
  apply memℓp_gen
  exact (Equiv.summable_iff e.symm).2
    ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp f))

/-- The underlying linear equivalence of `ℓ²` reindexing. -/
noncomputable def lpCongrLeftLinear (e : α ≃ β) :
    lp (fun _ : α ↦ ℝ) 2 ≃ₗ[ℝ] lp (fun _ : β ↦ ℝ) 2 where
  toFun f := ⟨fun b ↦ f (e.symm b), memℓp_comp_equiv e f⟩
  invFun f := ⟨fun a ↦ f (e.symm.symm a), memℓp_comp_equiv e.symm f⟩
  map_add' f g := by
    apply lp.ext
    funext b
    change (⇑(f + g)) (e.symm b) = f (e.symm b) + g (e.symm b)
    rw [lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext b
    change (⇑(c • f)) (e.symm b) = c • f (e.symm b)
    rw [lp.coeFn_smul, Pi.smul_apply]
  left_inv f := by
    apply lp.ext
    funext a
    change f (e.symm (e.symm.symm a)) = f a
    rw [Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext b
    change f (e.symm.symm (e.symm b)) = f b
    rw [Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Reindexing real `ℓ²` along an equivalence of index types is a linear
isometry. -/
noncomputable def lpCongrLeft (e : α ≃ β) :
    lp (fun _ : α ↦ ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : β ↦ ℝ) 2 :=
  (lpCongrLeftLinear e).isometryOfInner (by
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact Equiv.tsum_eq e.symm fun a ↦ ⟪f a, g a⟫_ℝ)

@[simp] theorem lpCongrLeft_apply (e : α ≃ β)
    (f : lp (fun _ : α ↦ ℝ) 2) (b : β) :
    lpCongrLeft e f b = f (e.symm b) := rfl

/-- Reindexing transports point masses. -/
theorem lpCongrLeft_single [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (i : α) (c : ℝ) :
    lpCongrLeft e (lp.single 2 i c) = lp.single 2 (e i) c := by
  apply lp.ext
  funext b
  have h1 : (lpCongrLeft e (lp.single 2 i c) : ∀ _ : β, ℝ) b =
      (lp.single 2 i c : ∀ _ : α, ℝ) (e.symm b) := rfl
  rw [h1, lp.coeFn_single, lp.coeFn_single]
  rcases eq_or_ne b (e i) with rfl | hb
  · rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hb,
      Pi.single_eq_of_ne fun h ↦ hb (by rw [← h, Equiv.apply_symm_apply])]

variable (G : Type u) [Group G] (A : Type u) [MulAction G A]

/-- The orthogonal permutation representation of a group action on the real
`ℓ²` space of the acted-on set. -/
noncomputable def permutationRepresentation :
    G →* (lp (fun _ : A ↦ ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : A ↦ ℝ) 2) where
  toFun g := lpCongrLeft (MulAction.toPerm g)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply lp.ext
    funext b
    change f ((MulAction.toPerm (1 : G)).symm b) = f b
    apply congrArg
    change (1 : G)⁻¹ • b = b
    simp
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    apply lp.ext
    funext b
    change f ((MulAction.toPerm (g * h)).symm b) =
      f ((MulAction.toPerm h).symm ((MulAction.toPerm g).symm b))
    apply congrArg
    change (g * h)⁻¹ • b = h⁻¹ • (g⁻¹ • b)
    rw [mul_inv_rev, mul_smul]

@[simp] theorem permutationRepresentation_apply (g : G)
    (f : lp (fun _ : A ↦ ℝ) 2) (b : A) :
    permutationRepresentation G A g f b = f (g⁻¹ • b) := rfl

/-- Property `(T)` produces a finite symmetric generating set containing the
identity.  The Kazhdan pair is tested on the `ℓ²` permutation representation
of the coset space of the subgroup its finite set generates. -/
theorem exists_symmetric_generating_finset
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ S : Finset G, 1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set G) = ⊤ := by
  classical
  obtain ⟨Q, ε, hε, hpair⟩ := hT
  set H : Subgroup G := Subgroup.closure (Q : Set G) with hH
  let rho := permutationRepresentation G (G ⧸ H)
  set x : lp (fun _ : G ⧸ H ↦ ℝ) 2 :=
    lp.single 2 (QuotientGroup.mk 1) 1 with hx
  have hxnorm : ‖x‖ = 1 := by
    rw [hx, lp.norm_single (by norm_num)]
    exact norm_one
  have hxfix : ∀ q ∈ Q, rho q x = x := by
    intro q hq
    have hq' : q ∈ H := Subgroup.subset_closure hq
    have hcoset : MulAction.toPerm q (QuotientGroup.mk (1 : G) : G ⧸ H) =
        QuotientGroup.mk 1 := by
      change q • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.2 (by simpa using H.inv_mem hq')
    calc
      rho q x = lp.single 2 (MulAction.toPerm q
          (QuotientGroup.mk (1 : G) : G ⧸ H)) 1 :=
        lpCongrLeft_single (MulAction.toPerm q) (QuotientGroup.mk 1) 1
      _ = x := by rw [hcoset]
  have hmove : ∀ q ∈ Q, ‖rho q x - x‖ < ε := by
    intro q hq
    rw [hxfix q hq, sub_self, norm_zero]
    exact hε
  obtain ⟨y, hy0, hyfix⟩ := hpair _ rho x hxnorm hmove
  have hconst : ∀ b : G ⧸ H, y b = y (QuotientGroup.mk 1) := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg
      (fun z : lp (fun _ : G ⧸ H ↦ ℝ) 2 ↦ z (QuotientGroup.mk g)) (hyfix g)
    change y ((MulAction.toPerm g).symm (QuotientGroup.mk g)) =
      y (QuotientGroup.mk g) at h
    rw [← h]
    apply congrArg
    change g⁻¹ • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  have hc : y (QuotientGroup.mk 1) ≠ 0 := by
    intro h0
    apply hy0
    apply lp.ext
    funext b
    rw [hconst b, h0]
    rfl
  have hsum : Summable fun b : G ⧸ H ↦ ‖y b‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).1 (lp.memℓp y)
  rw [show (fun b : G ⧸ H ↦ ‖y b‖ ^ (2 : ℝ≥0∞).toReal) =
      fun _ : G ⧸ H ↦ ‖y (QuotientGroup.mk 1)‖ ^ (2 : ℝ≥0∞).toReal from
    funext fun b ↦ by rw [hconst b]] at hsum
  haveI : Finite (G ⧸ H) :=
    Finite.of_summable_const
      (Real.rpow_pos_of_pos (norm_pos_iff.2 hc) _) hsum
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let T : Finset G := Finset.univ.image fun b : G ⧸ H ↦ b.out
  let S₀ : Finset G := Q ∪ T
  refine ⟨(S₀ ∪ S₀.image (·⁻¹)) ∪ {1}, by simp, ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_union, Finset.mem_image,
      Finset.mem_singleton] at hg ⊢
    rcases hg with (hg | ⟨a, ha, rfl⟩) | rfl
    · exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
    · exact Or.inl (Or.inl (by simpa using ha))
    · exact Or.inr (by simp)
  · apply top_unique
    intro g _
    have hQle : (Q : Set G) ⊆
        ((S₀ ∪ S₀.image (·⁻¹)) ∪ {1} : Finset G) := by
      intro q hq
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (Or.inl (Finset.mem_union_left _ (by exact_mod_cast hq)))
    have hHle : H ≤ Subgroup.closure
        (((S₀ ∪ S₀.image (·⁻¹)) ∪ {1} : Finset G) : Set G) := by
      rw [hH]
      exact Subgroup.closure_mono hQle
    have houtT : (QuotientGroup.mk g : G ⧸ H).out ∈ S₀ :=
      Finset.mem_union_right _
        (Finset.mem_image.2 ⟨QuotientGroup.mk g, Finset.mem_univ _, rfl⟩)
    have houtS : (QuotientGroup.mk g : G ⧸ H).out ∈ Subgroup.closure
        (((S₀ ∪ S₀.image (·⁻¹)) ∪ {1} : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (Or.inl houtT)
    have hmemH : (QuotientGroup.mk g : G ⧸ H).out⁻¹ * g ∈ H := by
      have hout : (QuotientGroup.mk ((QuotientGroup.mk g : G ⧸ H).out) :
          G ⧸ H) = QuotientGroup.mk g := QuotientGroup.out_eq' _
      exact QuotientGroup.eq.1 hout
    have := mul_mem houtS (hHle hmemH)
    simpa using this

end KazhdanFiniteGeneration

end NonsoficGroupsExist
