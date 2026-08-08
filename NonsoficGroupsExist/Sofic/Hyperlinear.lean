import NonsoficGroupsExist.Sofic.HyperlinearMetric
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import NonsoficGroupsExist.Sofic.SoficPositiveControl

/-!
# Hyperlinear groups, and one direction of Pestov's Question 3.4

A group is *hyperlinear* when every finite subset admits arbitrarily accurate
approximately multiplicative, separated models by **unitary matrices** under the
normalized Hilbert--Schmidt metric.  It is *sofic* when the same holds with
**permutation** matrices under the normalized Hamming metric.  Soficity implies
hyperlinearity (Elek--Szabó, Math. Ann. 332 (2005)); whether the converse holds
is Open Question 3.4 of Pestov's survey and is open.

This file formalizes the implication that holds.

The proof is exactly two facts, and both are already available.

* `Equiv.Perm.permMatrixHom` (Mathlib) is a genuine monoid homomorphism
  `Perm Y →* Matrix Y Y ℂ`, sending `σ` to `σ⁻¹.permMatrix` -- the inverse
  because `permMatrix` itself is an *anti*-homomorphism.  So the passage from
  permutations to matrices creates no multiplicative defect of its own.
* `permMatrix_hsDistSq`: the normalized Hilbert--Schmidt distance between two
  permutation matrices is exactly twice the normalized Hamming distance between
  the permutations.  This is `HyperlinearMetric.permMatrix_dist_sq_eq` over `ℂ`:
  each row of the difference is a difference of two standard basis vectors,
  contributing `0` when the permutations agree there and `2` when they do not.

Consequently a sofic model with accuracy `ε/2` *is* a hyperlinear model with
accuracy `ε`, after replacing each permutation by its matrix.  The two metrics
are the same metric; the factor `2` is the whole of the translation.

**The converse is Question 3.4 and nothing here bears on it.**  What the file
records is that the implication which does hold holds for a completely
transparent reason, so that the difficulty of the open direction is not hiding
anywhere in the easy one.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## The normalized Hilbert--Schmidt distance -/

/-- Squared normalized Hilbert--Schmidt distance between two matrices indexed by
a finite model. -/
noncomputable def hsDistSq (Y : FiniteModel) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- Entries of a permutation matrix over `ℂ`. -/
theorem permMatrixC_entry (Y : FiniteModel) (σ : Equiv.Perm Y) (x y : Y) :
    (σ.permMatrix ℂ) x y = if σ x = y then (1 : ℂ) else 0 := by
  simp [Equiv.Perm.permMatrix]

/-- A row of the difference contributes `0` when the permutations agree there
and `2` when they disagree: two distinct standard basis vectors. -/
theorem permMatrixC_row_normSq (Y : FiniteModel) (σ τ : Equiv.Perm Y) (x : Y) :
    (∑ y : Y, Complex.normSq ((σ.permMatrix ℂ) x y - (τ.permMatrix ℂ) x y))
      = if σ x = τ x then 0 else 2 := by
  classical
  have hentry : (∑ y : Y,
      Complex.normSq ((σ.permMatrix ℂ) x y - (τ.permMatrix ℂ) x y))
      = ∑ y : Y, Complex.normSq ((if σ x = y then (1 : ℂ) else 0)
          - (if τ x = y then 1 else 0)) := by
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [permMatrixC_entry, permMatrixC_entry]
  rw [hentry]
  by_cases h : σ x = τ x
  · simp [h]
  · rw [if_neg h]
    have hterm : ∀ y : Y, Complex.normSq ((if σ x = y then (1 : ℂ) else 0)
        - (if τ x = y then 1 else 0))
        = (if σ x = y then (1 : ℝ) else 0) + (if τ x = y then 1 else 0) := by
      intro y
      by_cases h1 : σ x = y <;> by_cases h2 : τ x = y <;> simp_all
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_add_distrib]
    norm_num

/-- **The metric translation.**  The squared normalized Hilbert--Schmidt
distance between permutation matrices is twice the normalized Hamming distance
between the permutations. -/
theorem permMatrix_hsDistSq (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    hsDistSq Y (σ.permMatrix ℂ) (τ.permMatrix ℂ)
      = 2 * hammingDistance Y σ τ := by
  classical
  have hsum : (∑ x : Y, ∑ y : Y,
      Complex.normSq ((σ.permMatrix ℂ) x y - (τ.permMatrix ℂ) x y))
      = 2 * (hammingDisagreement σ τ).card := by
    rw [Finset.sum_congr rfl fun x _ ↦ permMatrixC_row_normSq Y σ τ x]
    have hrw : ∀ x : Y, (if σ x = τ x then (0 : ℝ) else 2)
        = 2 * (if x ∈ hammingDisagreement σ τ then (1 : ℝ) else 0) := by
      intro x
      by_cases h : σ x = τ x <;> simp [mem_hammingDisagreement, h]
    rw [Finset.sum_congr rfl fun x _ ↦ hrw x, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite_mem]
    simp
  rw [hsDistSq, hsum, hammingDistance]
  ring

/-! ## Inverses do not move the Hamming distance -/

/-- Inverting both permutations permutes the disagreement set, via `y ↦ σ⁻¹ y`. -/
theorem hammingDisagreement_inv_card (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    (hammingDisagreement σ⁻¹ τ⁻¹).card = (hammingDisagreement σ τ).card := by
  classical
  refine Finset.card_bij (fun y _ ↦ σ⁻¹ y) ?_ ?_ ?_
  · intro y hy
    rw [mem_hammingDisagreement] at hy ⊢
    intro hcon
    apply hy
    have hy' : σ (σ⁻¹ y) = y := by simp
    rw [hy'] at hcon
    have hstep : τ⁻¹ y = σ⁻¹ y := by
      conv_lhs => rw [hcon]
      simp
    exact hstep.symm
  · intro a _ b _ hab
    have := congrArg (fun z ↦ σ z) hab
    simpa using this
  · intro x hx
    rw [mem_hammingDisagreement] at hx
    refine ⟨σ x, ?_, by simp⟩
    rw [mem_hammingDisagreement]
    intro hcon
    apply hx
    have hxx : σ⁻¹ (σ x) = x := by simp
    rw [hxx] at hcon
    have := congrArg (fun z ↦ τ z) hcon
    simpa using this.symm

theorem hammingDistance_inv (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    hammingDistance Y σ⁻¹ τ⁻¹ = hammingDistance Y σ τ := by
  rw [hammingDistance, hammingDistance, hammingDisagreement_inv_card]

/-! ## Hyperlinear models -/

/-- A finite unitary model on a prescribed finite subset, in the normalized
Hilbert--Schmidt metric.  The separation constant is `2 - ε` because the
translation from Hamming doubles distances: perfectly separated permutations
sit at squared Hilbert--Schmidt distance `2`. -/
structure HyperlinearModel (G : Type*) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hsDistSq carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    2 - ε ≤ hsDistSq carrier (map g) (map h)

/-- Hyperlinearity: unitary models of every accuracy on every finite set. -/
def IsHyperlinear (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (HyperlinearModel G F ε)

variable {G : Type*} [Group G]

/-- A permutation matrix is unitary: its conjugate transpose is the matrix of
the inverse permutation, and `permMatrix` is an anti-homomorphism. -/
theorem permMatrix_mem_unitaryGroup (Y : FiniteModel) (σ : Equiv.Perm Y) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup Y ℂ := by
  classical
  have hconj : (σ.permMatrix ℂ)ᴴ = (σ⁻¹).permMatrix ℂ := by
    ext i j
    simp [Equiv.Perm.permMatrix, Matrix.conjTranspose_apply, eq_comm,
      Equiv.eq_symm_apply]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hconj,
    ← Matrix.permMatrix_mul]
  simp

/-- **Soficity implies hyperlinearity.**  A sofic model of accuracy `ε/2`
becomes a hyperlinear model of accuracy `ε` under `σ ↦ σ⁻¹.permMatrix`: that map
is a genuine homomorphism, and it doubles the metric exactly. -/
theorem isHyperlinear_of_isSofic (h : IsSofic G) : IsHyperlinear G := by
  classical
  intro F ε hε
  obtain ⟨M⟩ := h F (ε / 2) (by positivity)
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ (M.map g)⁻¹.permMatrix ℂ
    isUnitary := fun g ↦ permMatrix_mem_unitaryGroup M.carrier _
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h' hh'
    have hhom : ((M.map g)⁻¹.permMatrix ℂ) * ((M.map h')⁻¹.permMatrix ℂ)
        = ((M.map g * M.map h')⁻¹).permMatrix ℂ := by
      rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]
    rw [hhom, permMatrix_hsDistSq, hammingDistance_inv]
    have hmul := M.multiplicative g hg h' hh'
    linarith
  · intro g hg h' hh' hne
    rw [permMatrix_hsDistSq, hammingDistance_inv]
    have hsep := M.separated g hg h' hh' hne
    linarith

/-- Positive control: finite groups are hyperlinear.  Without this,
`IsHyperlinear` would be a predicate nothing is known to satisfy, and a theorem
refuting it would be equally consistent with it being unsatisfiable. -/
theorem isHyperlinear_of_finite (G : Type) [Group G] [Finite G] :
    IsHyperlinear G :=
  isHyperlinear_of_isSofic (isSofic_of_finite G)

/-- A closed hyperlinear model, so that `HyperlinearModel` is not a certificate
nothing is ever known to satisfy: the one-point model of the trivial group. -/
noncomputable def trivialHyperlinearModel (F : Finset PUnit) :
    HyperlinearModel PUnit F 0 where
  carrier := ⟨PUnit, inferInstance, inferInstance⟩
  nonempty := by simp
  map := fun _ ↦ 1
  isUnitary := fun _ ↦ Submonoid.one_mem _
  multiplicative := by
    intro g _ h _
    simp [hsDistSq]
  separated := by
    intro g _ h _ hne
    exact absurd (Subsingleton.elim g h) hne

/-- The endpoint reading: a group that is not hyperlinear is not sofic.  The
converse of `isHyperlinear_of_isSofic` is Pestov's Question 3.4 and is open. -/
theorem not_isSofic_of_not_isHyperlinear (h : ¬ IsHyperlinear G) : ¬ IsSofic G :=
  fun hs ↦ h (isHyperlinear_of_isSofic hs)

/-! ## Hyperlinearity passes to subgroups

Remark `rem:hyperlinear` argues that the nonsofic witness of Theorem~A is not a
neutral test object for Question 3.4: it contains a copy of Thompson's `F`, and
hyperlinearity passes to subgroups, so proving the witness hyperlinear would
prove `F` hyperlinear -- a long-standing open problem.  That argument turns on
the monotonicity, which is proved here.

The proof is a restriction and nothing more.  An injective homomorphism carries
a finite subset of the subgroup to a finite subset of the ambient group; a model
there restricts along the map; multiplicativity transports because the map is a
homomorphism, and separation transports because it is injective.
-/

/-- **A model restricts along an injective homomorphism.** -/
noncomputable def HyperlinearModel.comap {H : Type*} [Group H] (ι : H →* G)
    (hι : Function.Injective ι) (F : Finset H) {ε : ℝ} [DecidableEq G]
    (M : HyperlinearModel G (F.image ι) ε) : HyperlinearModel H F ε where
  carrier := M.carrier
  nonempty := M.nonempty
  map := fun h ↦ M.map (ι h)
  isUnitary := fun h ↦ M.isUnitary (ι h)
  multiplicative := by
    intro g hg h hh
    show hsDistSq M.carrier (M.map (ι (g * h))) (M.map (ι g) * M.map (ι h)) ≤ ε
    rw [map_mul]
    exact M.multiplicative (ι g) (Finset.mem_image_of_mem ι hg)
      (ι h) (Finset.mem_image_of_mem ι hh)
  separated := by
    intro g hg h hh hne
    exact M.separated (ι g) (Finset.mem_image_of_mem ι hg)
      (ι h) (Finset.mem_image_of_mem ι hh) (fun hcon ↦ hne (hι hcon))

/-- **Hyperlinearity passes to subgroups**, and more generally along any
injective homomorphism.  This is the step Remark `rem:hyperlinear` uses to say
that proving the nonsofic witness hyperlinear would prove Thompson's `F`
hyperlinear. -/
theorem isHyperlinear_of_injective {H : Type*} [Group H] (ι : H →* G)
    (hι : Function.Injective ι) (hG : IsHyperlinear G) : IsHyperlinear H := by
  classical
  intro F ε hε
  obtain ⟨M⟩ := hG (F.image ι) ε hε
  exact ⟨HyperlinearModel.comap ι hι F M⟩

/-- **Non-hyperlinearity of a subgroup defeats soficity of the whole group.**
Composing the monotonicity with `not_isSofic_of_not_isHyperlinear`: if any
subgroup fails to be hyperlinear then the ambient group is not sofic.  This is
the direction in which a single hard subgroup propagates outward, and it is why
the witness of Theorem~A containing Thompson's `F` cuts both ways -- it makes
the witness's hyperlinearity hard to prove, and it would make `F`'s failure, if
ever established, decide the witness. -/
theorem not_isSofic_of_subgroup_not_isHyperlinear {H : Type*} [Group H]
    (ι : H →* G) (hι : Function.Injective ι) (hH : ¬ IsHyperlinear H) :
    ¬ IsSofic G :=
  not_isSofic_of_not_isHyperlinear
    (fun hG ↦ hH (isHyperlinear_of_injective ι hι hG))

/-! ## Hyperlinearity is a local property

The definition quantifies over finite subsets, so it cannot see beyond the
subgroup a finite subset generates.  With the monotonicity above that gives the
standard locality statement: `G` is hyperlinear as soon as every finite subset
lies in the image of an injective homomorphism from a hyperlinear group.

The construction extends a model of the source to the whole of `G` by sending
everything outside the image to the identity.  The guard has to be membership in
the *image* rather than in the finite set: the multiplicativity condition names
`g * h`, which need not lie in the finite set but does lie in the image, that
being a subgroup.
-/

/-- **Locality.**  With `isHyperlinear_of_injective` this makes hyperlinearity
local: it holds for `G` exactly when it holds for the subgroups generated by
finite subsets. -/
theorem isHyperlinear_of_local
    (h : ∀ F : Finset G, ∃ (H : Type) (_ : Group H) (ι : H →* G),
      Function.Injective ι ∧ IsHyperlinear H ∧ ∀ g ∈ F, g ∈ Set.range ι) :
    IsHyperlinear G := by
  classical
  intro F ε hε
  obtain ⟨H, _, ι, hinj, hH, hcov⟩ := h F
  set ψ : G → H := Function.invFun ι with hψ
  have hψι : ∀ x : H, ψ (ι x) = x := fun x ↦ Function.leftInverse_invFun hinj x
  have hιψ : ∀ g ∈ Set.range ι, ι (ψ g) = g := by
    rintro g ⟨x, rfl⟩
    rw [hψι]
  set F' : Finset H := F.image ψ with hF'
  obtain ⟨M⟩ := hH F' ε hε
  have hmemF' : ∀ g ∈ F, ψ g ∈ F' := fun g hg ↦ Finset.mem_image_of_mem ψ hg
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ if g ∈ Set.range ι then M.map (ψ g) else 1
    isUnitary := ?_
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g
    by_cases hg : g ∈ Set.range ι
    · simpa [hg] using M.isUnitary (ψ g)
    · simp [hg]
  · intro g hg h hh
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    have hghr : g * h ∈ Set.range ι := by
      obtain ⟨a, rfl⟩ := hgr
      obtain ⟨b, rfl⟩ := hhr
      exact ⟨a * b, by rw [map_mul]⟩
    have hpsi : ψ (g * h) = ψ g * ψ h := by
      apply hinj
      rw [hιψ _ hghr, map_mul, hιψ _ hgr, hιψ _ hhr]
    simp only [if_pos hgr, if_pos hhr, if_pos hghr, hpsi]
    exact M.multiplicative _ (hmemF' g hg) _ (hmemF' h hh)
  · intro g hg h hh hne
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    simp only [if_pos hgr, if_pos hhr]
    refine M.separated _ (hmemF' g hg) _ (hmemF' h hh) ?_
    intro hcon
    exact hne (by rw [← hιψ _ hgr, ← hιψ _ hhr, hcon])

end NonsoficGroupsExist
