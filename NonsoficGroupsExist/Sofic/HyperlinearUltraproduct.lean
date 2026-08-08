import NonsoficGroupsExist.Sofic.PhasePropagation
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The unitary metric ultraproduct, and where its bridge is missing

`Sofic.SoficUltraproduct` builds `∏_𝒰 Sym(X i)`, the universal sofic group, and
proves the bridge in both directions: an injective homomorphism into such a
quotient makes a group sofic, and a sofic approximation is such an embedding.
The forward direction is amplification -- injectivity separates a pair by *some*
positive amount, never by the `1 - ε` the definition asks, and tensor powers
close that gap.

This file builds the unitary counterpart `∏_𝒰 U(X i)`.  The construction goes
through verbatim, and it goes through *without square roots*: the null
sequences are those whose squared Hilbert--Schmidt length vanishes, and the
three closure properties come from

* `hsNormSq_add_le`, the crude `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`, which is enough
  because a factor `2` cannot obstruct a limit;
* `hsNormSq_mul_left` and `hsNormSq_mul_right`, unitary invariance on both
  sides, which give inverse- and conjugation-invariance of the length.

What does **not** go through is the bridge.  `isSofic_of_soficEmbedding` runs on
tensor amplification, and `Sofic.HyperlinearAmplification` proves that
amplification is unavailable here: the `k`-th tensor power identifies unitaries
differing by a `k`-th root of unity, and `1` and `i·1` are maximally separated
with equal fourth powers.  So the unitary ultraproduct exists and is a group,
but the passage from *an embedding* to *a model with separation `2 - ε`* is not
elementary on this side.  It is available -- by Rădulescu's theorem, through
`R^ω` -- and that is precisely the asymmetry recorded in
`docs/PHASES.md`: the same statement, elementary in one category and a von
Neumann algebra theorem in the other.
-/

namespace NonsoficGroupsExist

open Filter Matrix

/-! ## The squared Hilbert--Schmidt length -/

/-- Squared displacement of a unitary from the identity. -/
noncomputable def hsLengthSq (Y : FiniteModel) (u : Matrix Y Y ℂ) : ℝ :=
  hsNormSq Y (u - 1)

@[simp] theorem hsLengthSq_one (Y : FiniteModel) :
    hsLengthSq Y 1 = 0 := by
  rw [hsLengthSq, sub_self]
  simp [hsNormSq]

theorem hsLengthSq_nonneg (Y : FiniteModel) (u : Matrix Y Y ℂ) :
    0 ≤ hsLengthSq Y u :=
  hsNormSq_nonneg _ _

/-- **The crude triangle inequality for the length.**  A factor `2` per step is
harmless for a limit, which is all the null subgroup needs. -/
theorem hsLengthSq_mul_le (Y : FiniteModel) {u v : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsLengthSq Y (u * v) ≤ 2 * hsLengthSq Y u + 2 * hsLengthSq Y v := by
  have hsplit : u * v - 1 = u * (v - 1) + (u - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  calc hsLengthSq Y (u * v) = hsNormSq Y (u * (v - 1) + (u - 1)) := by
        rw [hsLengthSq, hsplit]
    _ ≤ 2 * hsNormSq Y (u * (v - 1)) + 2 * hsNormSq Y (u - 1) :=
        hsNormSq_add_le _ _ _
    _ = 2 * hsLengthSq Y v + 2 * hsLengthSq Y u := by
        rw [hsNormSq_mul_left Y hu hY, hsLengthSq, hsLengthSq]
    _ = 2 * hsLengthSq Y u + 2 * hsLengthSq Y v := by ring

/-- Conjugate transposition -- inversion, for a unitary -- does not move the
length. -/
theorem hsLengthSq_conjTranspose (Y : FiniteModel) {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsLengthSq Y uᴴ = hsLengthSq Y u := by
  have hcu : uᴴ * u = 1 := by
    have h := hu
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hcmem : uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hcu
  have hsplit : uᴴ - 1 = (-1 : ℂ) • (uᴴ * (u - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hcu, smul_sub, neg_smul, neg_smul,
      one_smul, one_smul]
    abel
  rw [hsLengthSq, hsplit, hsNormSq_smul, hsNormSq_mul_left Y hcmem hY,
    hsLengthSq]
  norm_num

/-- **The identity that makes the quotient metric the model metric**, the exact
counterpart of `hammingLength_inv_mul` on the permutation side: for unitary `w`,
the length of `w* v` is the squared distance from `v` to `w`.  So the metric the
ultraproduct carries is the one the models are measured in, and the null
subgroup is exactly the sequences that converge to the identity in it. -/
theorem hsLengthSq_conjTranspose_mul (Y : FiniteModel) {v w : Matrix Y Y ℂ}
    (hw : w ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsLengthSq Y (wᴴ * v) = hsDistSq Y v w := by
  have hww : wᴴ * w = 1 := by
    have h := hw
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hwmem : wᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hww
  have hsplit : wᴴ * v - 1 = wᴴ * (v - w) := by
    rw [Matrix.mul_sub, hww]
  rw [hsLengthSq, hsplit, hsNormSq_mul_left Y hwmem hY]
  rfl

/-! ## The null subgroup -/

variable {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)

/-- Sequences of unitaries whose squared length vanishes along `𝒰`. -/
def IsNullUnitarySeq
    (u : ∀ i, Matrix.unitaryGroup (X i) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι), hsLengthSq (X i) (u i) < ε

/-- Positive control: the constant identity sequence is null. -/
theorem isNullUnitarySeq_one : IsNullUnitarySeq 𝒰 X 1 := by
  intro ε hε
  filter_upwards with i
  show hsLengthSq (X i) (1 : Matrix.unitaryGroup (X i) ℂ) < ε
  have : ((1 : Matrix.unitaryGroup (X i) ℂ) : Matrix (X i) (X i) ℂ) = 1 := rfl
  rw [this, hsLengthSq_one]
  exact hε

/-- The null sequences, as a subgroup of the product, when every model is
nonempty. -/
def nullUnitarySubgroup (hX : ∀ i, 0 < Fintype.card (X i)) :
    Subgroup (∀ i, Matrix.unitaryGroup (X i) ℂ) where
  carrier := {u | IsNullUnitarySeq 𝒰 X u}
  one_mem' := isNullUnitarySeq_one 𝒰 X
  mul_mem' := by
    intro u v hu hv ε hε
    filter_upwards [hu (ε / 4) (by linarith), hv (ε / 4) (by linarith)]
      with i hi hj
    show hsLengthSq (X i) ((u i : Matrix (X i) (X i) ℂ) * v i) < ε
    calc hsLengthSq (X i) ((u i : Matrix (X i) (X i) ℂ) * v i)
        ≤ 2 * hsLengthSq (X i) (u i) + 2 * hsLengthSq (X i) (v i) :=
          hsLengthSq_mul_le (X i) (u i).2 (hX i)
      _ < 2 * (ε / 4) + 2 * (ε / 4) := by linarith
      _ = ε := by ring
  inv_mem' := by
    intro u hu ε hε
    filter_upwards [hu ε hε] with i hi
    show hsLengthSq (X i) (((u i)⁻¹ : Matrix.unitaryGroup (X i) ℂ)) < ε
    have hcoe : (((u i)⁻¹ : Matrix.unitaryGroup (X i) ℂ) :
        Matrix (X i) (X i) ℂ) = (u i : Matrix (X i) (X i) ℂ)ᴴ := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    rw [hcoe, hsLengthSq_conjTranspose (X i) (u i).2 (hX i)]
    exact hi

/-- Conjugation does not move the length. -/
theorem hsLengthSq_conj (Y : FiniteModel) {t u : Matrix Y Y ℂ}
    (ht : t ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsLengthSq Y (t * u * tᴴ) = hsLengthSq Y u := by
  have htt : t * tᴴ = 1 := by
    have h := ht
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have htmem : tᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact htt
  have hsplit : t * u * tᴴ - 1 = t * (u - 1) * tᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, htt]
  rw [hsLengthSq, hsplit, hsNormSq_mul_right Y htmem,
    hsNormSq_mul_left Y ht hY, hsLengthSq]

instance nullUnitarySubgroup_normal (hX : ∀ i, 0 < Fintype.card (X i)) :
    (nullUnitarySubgroup 𝒰 X hX).Normal where
  conj_mem := by
    intro u hu t ε hε
    filter_upwards [hu ε hε] with i hi
    show hsLengthSq (X i) ((t i * u i * (t i)⁻¹ :
      Matrix.unitaryGroup (X i) ℂ)) < ε
    have hcoe : ((t i * u i * (t i)⁻¹ : Matrix.unitaryGroup (X i) ℂ) :
        Matrix (X i) (X i) ℂ)
        = (t i : Matrix (X i) (X i) ℂ) * (u i : Matrix (X i) (X i) ℂ)
          * (t i : Matrix (X i) (X i) ℂ)ᴴ := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    rw [hcoe, hsLengthSq_conj (X i) (t i).2 (hX i)]
    exact hi

/-- **The universal hyperlinear group** over `X` along `𝒰`: the metric
ultraproduct of the finite unitary groups. -/
abbrev UniversalHyperlinear (hX : ∀ i, 0 < Fintype.card (X i)) : Type _ :=
  (∀ i, Matrix.unitaryGroup (X i) ℂ) ⧸ nullUnitarySubgroup 𝒰 X hX

/-! ## What injectivity of the induced map would need -/

/-- **In a separated model every nontrivial test element is uniformly far from
the identity.**  This is the estimate an embedding's injectivity consumes: the
sequence attached to `g ≠ 1` has length bounded below, so it is not null and its
class in the ultraproduct is not trivial. -/
theorem hsLengthSq_ge_of_separated {G : Type*} [Group G] {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) (hε : 0 < ε) (hεle : ε ≤ 1 / 10000)
    {g : G} (hg : g ∈ F) (h1F : (1 : G) ∈ F) (hgne : g ≠ 1) :
    2 - ε - 1 / 50 ≤ hsLengthSq M.carrier (M.map g) := by
  have hre := re_normTrace_le_of_separated M hε hεle hg h1F hgne
  have hone : (1 : Matrix M.carrier M.carrier ℂ)
      ∈ Matrix.unitaryGroup M.carrier ℂ := Submonoid.one_mem _
  have hdist : hsDistSq M.carrier (M.map g) 1
      = 2 - 2 * (normTrace M.carrier (M.map g * (1 : Matrix M.carrier
        M.carrier ℂ)ᴴ)).re :=
    hsDistSq_of_unitary M.carrier (M.isUnitary g) hone M.nonempty
  have hsimp : M.map g * (1 : Matrix M.carrier M.carrier ℂ)ᴴ = M.map g := by
    rw [Matrix.conjTranspose_one, Matrix.mul_one]
  rw [hsimp] at hdist
  show 2 - ε - 1 / 50 ≤ hsNormSq M.carrier (M.map g - 1)
  have hrw : hsNormSq M.carrier (M.map g - 1)
      = hsDistSq M.carrier (M.map g) 1 := rfl
  rw [hrw, hdist]
  linarith

end NonsoficGroupsExist
