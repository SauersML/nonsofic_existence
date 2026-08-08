import NonsoficGroupsExist.Sofic.PhasePropagation
import NonsoficGroupsExist.Sofic.SoficUltraproduct
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

/-! ## From an approximation to an embedding -/

section Converse

variable {G : Type*} [Group G]

/-- A sequence of unitary models of growing accuracy, in the shape the
ultraproduct consumes. -/
structure HyperlinearApproximation (G : Type*) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  map : ∀ n, G → Matrix.unitaryGroup (model n) ℂ
  asymptoticallyMultiplicative : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    hsDistSq (model n) (map n (g * h)) ((map n g : Matrix (model n) (model n) ℂ)
      * map n h) ≤ ε
  separatedEventually : ∀ g h : G, g ≠ h → ∃ N, ∀ n ≥ N,
    1 ≤ hsDistSq (model n) (map n g) (map n h)

/-- A closed inhabitant: the one-point models of the trivial group. -/
noncomputable def trivialHyperlinearApproximation :
    HyperlinearApproximation PUnit where
  model := fun _ ↦ ⟨PUnit, inferInstance, inferInstance⟩
  modelNonempty := fun _ ↦ by simp
  map := fun _ _ ↦ 1
  asymptoticallyMultiplicative := by
    intro g h ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    show hsDistSq _ (1 : Matrix _ _ ℂ) ((1 : Matrix _ _ ℂ) * 1) ≤ ε
    rw [Matrix.mul_one, hsDistSq_self]
    exact hε.le
  separatedEventually := by
    intro g h hne
    exact absurd (Subsingleton.elim g h) hne

/-- Coercion of an inverse-times-element in the unitary group. -/
theorem coe_inv_mul (Y : FiniteModel) (a b : Matrix.unitaryGroup Y ℂ) :
    ((a⁻¹ * b : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)
      = (a : Matrix Y Y ℂ)ᴴ * b := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

/-- **A hyperlinear approximation is a hyperlinear embedding.**  The unitaries,
read as one sequence per group element, define an injective homomorphism into
the universal hyperlinear group over its models.  This is the direction that
does not need amplification, and it is therefore the direction that survives
the phase collapse. -/
theorem exists_hyperlinearEmbedding_of_approximation
    (S : HyperlinearApproximation G) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ f : G →* UniversalHyperlinear 𝒰 S.model S.modelNonempty,
      Function.Injective f := by
  classical
  have hlen : ∀ (n : ℕ) (a b : Matrix.unitaryGroup (S.model n) ℂ),
      hsLengthSq (S.model n) ((a⁻¹ * b : Matrix.unitaryGroup (S.model n) ℂ))
        = hsDistSq (S.model n) b a := by
    intro n a b
    rw [coe_inv_mul]
    exact hsLengthSq_conjTranspose_mul (S.model n) a.2 (S.modelNonempty n)
  have hnull : ∀ g h : G,
      (fun n ↦ S.map n g * S.map n h)⁻¹ * (fun n ↦ S.map n (g * h))
        ∈ nullUnitarySubgroup 𝒰 S.model S.modelNonempty := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    show hsLengthSq (S.model n)
      (((S.map n g * S.map n h)⁻¹ * S.map n (g * h) :
        Matrix.unitaryGroup (S.model n) ℂ)) < ε
    rw [hlen n (S.map n g * S.map n h) (S.map n (g * h))]
    have hcoe : ((S.map n g * S.map n h : Matrix.unitaryGroup (S.model n) ℂ) :
        Matrix (S.model n) (S.model n) ℂ)
        = (S.map n g : Matrix (S.model n) (S.model n) ℂ) * S.map n h := rfl
    rw [hcoe]
    have := hN n hn
    linarith
  refine ⟨MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ S.map n g)) ?_, ?_⟩
  · intro g h
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq.mpr (hnull g h)).symm
  · intro g h hgh
    by_contra hne
    obtain ⟨N, hN⟩ := S.separatedEventually g h hne
    have hfar : ∀ᶠ n in (𝒰 : Filter ℕ),
        (1 : ℝ) ≤ hsDistSq (S.model n) (S.map n g) (S.map n h) :=
      eventually_of_atTop hcof N hN
    have hgh' : (QuotientGroup.mk (fun n ↦ S.map n g) :
        UniversalHyperlinear 𝒰 S.model S.modelNonempty)
        = QuotientGroup.mk (fun n ↦ S.map n h) := hgh
    have hmem : (fun n ↦ S.map n h)⁻¹ * (fun n ↦ S.map n g)
        ∈ nullUnitarySubgroup 𝒰 S.model S.modelNonempty :=
      QuotientGroup.eq.mp hgh'.symm
    have hclose : ∀ᶠ n in (𝒰 : Filter ℕ),
        hsDistSq (S.model n) (S.map n g) (S.map n h) < 1 := by
      filter_upwards [hmem 1 (by norm_num)] with n hn
      rw [show hsLengthSq (S.model n)
          (((fun m ↦ S.map m h)⁻¹ * (fun m ↦ S.map m g) : ∀ m,
            Matrix.unitaryGroup (S.model m) ℂ) n)
          = hsDistSq (S.model n) (S.map n g) (S.map n h) from
        hlen n (S.map n h) (S.map n g)] at hn
      exact hn
    obtain ⟨n, hn₁, hn₂⟩ := (hfar.and hclose).exists
    linarith

/-- **Hyperlinearity supplies an approximation.**  For a countable group,
exhausting by finite test sets and shrinking the accuracy turns the local
definition into the sequential one the ultraproduct consumes. -/
theorem exists_hyperlinearApproximation_of_isHyperlinear [Countable G]
    (h : IsHyperlinear G) : Nonempty (HyperlinearApproximation G) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  set F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
    with hFdef
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, hi⟩ := he g
    refine ⟨i, fun n hn ↦ hFmono hn ?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.self_mem_range_succ i, hi⟩)
  have heps : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := by
    intro n; positivity
  set M : ∀ n : ℕ, HyperlinearModel G (F n) (1 / (n + 1)) :=
    fun n ↦ (h (F n) (1 / (n + 1)) (heps n)).some with hMdef
  refine ⟨{
    model := fun n ↦ (M n).carrier
    modelNonempty := fun n ↦ (M n).nonempty
    map := fun n g ↦ ⟨(M n).map g, (M n).isUnitary g⟩
    asymptoticallyMultiplicative := ?_
    separatedEventually := ?_ }⟩
  · intro g h' ε hε
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h'
    obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
    refine ⟨max (max Ng Nh) Ne, fun n hn ↦ ?_⟩
    have h1 : g ∈ F n := hNg n (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) hn)
    have h2 : h' ∈ F n := hNh n (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) hn)
    have hsmall : 1 / ((n : ℝ) + 1) ≤ ε := by
      have hNen : (Ne : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (le_max_right _ _) hn
      have : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at this
      linarith
    exact le_trans ((M n).multiplicative g h1 h' h2) hsmall
  · intro g h' hne
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h'
    refine ⟨max Ng Nh, fun n hn ↦ ?_⟩
    have h1 : g ∈ F n := hNg n (le_trans (le_max_left _ _) hn)
    have h2 : h' ∈ F n := hNh n (le_trans (le_max_right _ _) hn)
    have hsep := (M n).separated g h1 h' h2 hne
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith

end Converse

end NonsoficGroupsExist
