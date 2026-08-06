import NonsoficGroupsExist.Sofic.Sofic
import NonsoficGroupsExist.Sofic.LEF
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.Index

/-!
# LEF groups are sofic, and residually finite groups are LEF

The two positive inclusions of the approximation hierarchy, in the form this
library states them.

**LEF ⇒ sofic.**  A local embedding of a finite test set into a finite group
is *exactly* multiplicative and *exactly* injective, so the left-regular
representation of the target turns it into a permutation model of the best
possible quality: multiplicative defect `0`, and Hamming separation `1` —
left translations by distinct elements disagree everywhere.  The
quantifier-free heart of the argument is that the sofic definition asks for
approximations that local embeddings deliver exactly.

**Residually finite ⇒ LEF.**  A finite test set has finitely many nonidentity
difference quotients; a finite-index normal subgroup avoiding all of them
makes the quotient map injective on the set, and a quotient map is globally
multiplicative.  The finite quotient then acts on itself, giving the
permutation target the `IsLEF` definition asks for.

Together with `isSofic_of_finite`, these place the classical inclusions

  finite ⊆ residually finite ⊆ LEF ⊆ sofic

in the library.  The missing classical input for the quotient-nonclosure
theorem — residual finiteness of free groups — is not proved here.
-/

namespace NonsoficGroupsExist

variable {G : Type*} [Group G]

/-! ### Left-regular permutation models -/

section LeftRegular

variable {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]

/-- Left translation, as a permutation of the finite group. -/
def leftRegular (q : Q) : Equiv.Perm Q := Equiv.mulLeft q

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem leftRegular_apply (q x : Q) : leftRegular q x = q * x := rfl

omit [Fintype Q] [DecidableEq Q] in
theorem leftRegular_mul (q r : Q) :
    leftRegular (q * r) = leftRegular q * leftRegular r := by
  ext x
  simp [leftRegular]

/-- Left translations by distinct elements disagree at every point. -/
theorem leftRegular_disagreement_univ {q r : Q} (hqr : q ≠ r) :
    hammingDisagreement (leftRegular q) (leftRegular r) = Finset.univ := by
  ext x
  simp only [mem_hammingDisagreement, Finset.mem_univ, iff_true,
    leftRegular_apply]
  intro h
  exact hqr (mul_right_cancel h)

/-- The model carrier of a `FiniteModel` lives in `Type`, so this one is
stated there rather than for the ambient universe-polymorphic `Q`; it is only
ever applied to a permutation group of a `Fin n`. -/
theorem hammingDistance_leftRegular {Y : Type} [Group Y] [Fintype Y]
    [DecidableEq Y] {q r : Y} (hqr : q ≠ r) :
    hammingDistance ⟨Y, inferInstance, inferInstance⟩
      (leftRegular q) (leftRegular r) = 1 := by
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast Fintype.card_pos
  rw [hammingDistance, leftRegular_disagreement_univ hqr,
    Finset.card_univ, div_self (ne_of_gt hcard)]

end LeftRegular

/-! ### LEF implies sofic -/

/-- **LEF groups are sofic.**  The models produced are exact: multiplicative
defect zero and separation one, uniformly in the requested tolerance. -/
theorem isSofic_of_isLEF (h : IsLEF G) : IsSofic G := by
  classical
  intro F ε hε
  obtain ⟨n, f, hinj, hmul⟩ := h F
  refine ⟨{
    carrier := ⟨Equiv.Perm (Fin n), inferInstance, inferInstance⟩
    nonempty := Fintype.card_pos
    map := fun g => leftRegular (f g)
    multiplicative := by
      intro g hg k hk
      have hf : f (g * k) = f g * f k := hmul.map_mul g hg k hk
      rw [hf, leftRegular_mul, hammingDistance_self]
      exact le_of_lt hε
    separated := by
      intro g hg k hk hgk
      have hfk : f g ≠ f k := fun hcon => hgk (hinj hg hk hcon)
      rw [hammingDistance_leftRegular hfk]
      linarith }⟩

/-! ### Residually finite implies LEF -/

/-- The permutation form of a finite group: its left-regular image inside the
permutations of an enumeration of its elements. -/
noncomputable def finitePermForm {Q : Type*} [Group Q] [Fintype Q]
    [DecidableEq Q] (q : Q) : Equiv.Perm (Fin (Fintype.card Q)) :=
  ((Fintype.equivFin Q).permCongr (leftRegular q))

theorem finitePermForm_one {Q : Type*} [Group Q] [Fintype Q]
    [DecidableEq Q] : finitePermForm (1 : Q) = 1 := by
  ext x
  simp [finitePermForm, Equiv.permCongr_apply, leftRegular]

theorem finitePermForm_mul {Q : Type*} [Group Q] [Fintype Q]
    [DecidableEq Q] (q r : Q) :
    finitePermForm (q * r) = finitePermForm q * finitePermForm r := by
  ext x
  simp [finitePermForm, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    leftRegular]

theorem finitePermForm_injective {Q : Type*} [Group Q] [Fintype Q]
    [DecidableEq Q] :
    Function.Injective (finitePermForm (Q := Q)) := by
  intro q r hqr
  have h1 := congrArg (fun p => p ((Fintype.equivFin Q) 1)) hqr
  simp only [finitePermForm, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    leftRegular_apply, mul_one] at h1
  exact (Fintype.equivFin Q).injective h1

/-- **Residually finite groups are LEF.**  The local embedding is the
quotient by a finite-index normal subgroup avoiding the finitely many
nonidentity difference quotients of the test set, followed by the
left-regular permutation form of the finite quotient. -/
theorem isLEF_of_residuallyFinite [Group.ResiduallyFinite G] : IsLEF G := by
  classical
  intro s
  -- the nonidentity difference quotients of the test set
  set D : Finset G :=
    ((s ×ˢ s).filter fun p => p.1 ≠ p.2).image fun p => p.1⁻¹ * p.2 with hD
  have hD_ne_one : ∀ d ∈ D, d ≠ 1 := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hd
    rw [Finset.mem_filter] at hxy
    intro hcon
    exact hxy.2 (by
      have := congrArg (fun z => x * z) hcon
      simpa [mul_assoc] using this.symm)
  -- a finite-index normal subgroup avoiding each difference
  have hchoice : ∀ d : {x // x ∈ D}, ∃ N : Subgroup G,
      N.Normal ∧ N.FiniteIndex ∧ d.1 ∉ N := by
    intro d
    obtain ⟨H, hnotmem⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem d.1 (hD_ne_one d.1 d.2)
    exact ⟨H.toSubgroup, H.isNormal', H.isFiniteIndex', hnotmem⟩
  choose Nd hNd_normal hNd_index hNd_notmem using hchoice
  -- their intersection over the finitely many differences
  set N : Subgroup G := ⨅ d : {x // x ∈ D}, Nd d with hN
  haveI hN_normal : N.Normal := by
    constructor
    intro g hg x
    rw [hN, Subgroup.mem_iInf] at hg ⊢
    intro d
    exact (hNd_normal d).conj_mem g (hg d) x
  haveI : ∀ d : {x // x ∈ D}, (Nd d).FiniteIndex := hNd_index
  haveI hN_index : N.FiniteIndex := by
    rw [hN]
    exact Subgroup.finiteIndex_iInf hNd_index
  -- the finite quotient, with classical instances for the permutation form
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  letI : DecidableEq (G ⧸ N) := Classical.decEq _
  refine ⟨Fintype.card (G ⧸ N),
    fun g => finitePermForm (QuotientGroup.mk' N g), ?_, ?_⟩
  · -- injectivity on the test set: a collapse would put a difference
    -- quotient into `N`, hence into the subgroup chosen to avoid it
    intro x hx y hy hxy
    by_contra hne
    have hmem : x⁻¹ * y ∈ D := by
      rw [hD, Finset.mem_image]
      exact ⟨(x, y), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hne⟩, rfl⟩
    have hquot : QuotientGroup.mk' N x = QuotientGroup.mk' N y :=
      finitePermForm_injective hxy
    have hinN : x⁻¹ * y ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hquot]
      simp
    have hinNd : x⁻¹ * y ∈ Nd ⟨x⁻¹ * y, hmem⟩ := by
      rw [hN] at hinN
      exact Subgroup.mem_iInf.mp hinN ⟨x⁻¹ * y, hmem⟩
    exact hNd_notmem ⟨x⁻¹ * y, hmem⟩ hinNd
  · -- exact multiplicativity, from the quotient map and the permutation form
    constructor
    · rw [map_one, finitePermForm_one]
    · intro x _ y _
      rw [map_mul, finitePermForm_mul]

end NonsoficGroupsExist
