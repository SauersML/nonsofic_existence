import NonsoficGroupsExist.KOne.CodeScalarMoves

/-!
# Pencil-entry arithmetic under scalar moves

The five-coefficient pencil entry
`pE(a₀,a₁,c,b₀,b₁) = a₀•t₀ + a₁•t₁ + c•1 + (b₀•s₀ + b₁•s₁)` is
`k`-bilinear in the expected way: multiplying a code-pencil value by a
transported scalar matrix on the right (resp. left) multiplies the
five coefficient matrices by that matrix on the right (resp. left).
These are the `GL(k)`-normalization steps of the elimination at the
value level.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- The five-coefficient pencil entry. -/
noncomputable def pencilEntry (a₀ a₁ c b₀ b₁ : k) : A :=
  a₀ • L.t 0 + a₁ • L.t 1 + c • (1 : A) + (b₀ • L.s 0 + b₁ • L.s 1)

theorem smul_mul_algebraMap (x : k) (y : A) (μ : k) :
    (x • y) * algebraMap k A μ = (x * μ) • y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
    ← Algebra.commutes μ y]
  rw [← mul_assoc]

theorem algebraMap_mul_smul (μ : k) (x : k) (y : A) :
    algebraMap k A μ * (x • y) = (μ * x) • y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-- Right multiplication by a scalar acts on the coefficients. -/
theorem pencilEntry_mul_algebraMap (a₀ a₁ c b₀ b₁ μ : k) :
    (L.pencilEntry (k := k) a₀ a₁ c b₀ b₁ : A) * algebraMap k A μ =
      L.pencilEntry (k := k) (a₀ * μ) (a₁ * μ) (c * μ) (b₀ * μ)
        (b₁ * μ) := by
  unfold pencilEntry
  rw [add_mul, add_mul, add_mul, add_mul,
    smul_mul_algebraMap a₀ (L.t 0) μ,
    smul_mul_algebraMap a₁ (L.t 1) μ,
    smul_mul_algebraMap c 1 μ,
    smul_mul_algebraMap b₀ (L.s 0) μ,
    smul_mul_algebraMap b₁ (L.s 1) μ]

/-- Left multiplication by a scalar acts on the coefficients. -/
theorem algebraMap_mul_pencilEntry (μ a₀ a₁ c b₀ b₁ : k) :
    algebraMap k A μ * (L.pencilEntry (k := k) a₀ a₁ c b₀ b₁ : A) =
      L.pencilEntry (k := k) (μ * a₀) (μ * a₁) (μ * c) (μ * b₀)
        (μ * b₁) := by
  unfold pencilEntry
  rw [mul_add, mul_add, mul_add, mul_add,
    algebraMap_mul_smul μ a₀ (L.t 0),
    algebraMap_mul_smul μ a₁ (L.t 1),
    algebraMap_mul_smul μ c 1,
    algebraMap_mul_smul μ b₀ (L.s 0),
    algebraMap_mul_smul μ b₁ (L.s 1)]

/-- Sums of pencil entries collect coefficientwise. -/
theorem sum_pencilEntry {γ : Type*} (s : Finset γ)
    (a₀ a₁ c b₀ b₁ : γ → k) :
    ∑ l ∈ s, (L.pencilEntry (k := k) (a₀ l) (a₁ l) (c l) (b₀ l)
        (b₁ l) : A) =
      L.pencilEntry (k := k) (∑ l ∈ s, a₀ l) (∑ l ∈ s, a₁ l)
        (∑ l ∈ s, c l) (∑ l ∈ s, b₀ l) (∑ l ∈ s, b₁ l) := by
  unfold pencilEntry
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul,
    ← Finset.sum_smul, ← Finset.sum_smul]

omit [DecidableEq ι] in
/-- **Right scalar move**: multiplying a code pencil by a transported
scalar matrix multiplies the five coefficient matrices on the
right. -/
theorem pencilVal_mul_codeScalar
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (G : Matrix κ κ k) :
    (∑ i, ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
          (B₁ i j) * L.wordT (C.word j)) *
      L.codeScalar (k := k) C G =
    ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (∑ l, A₀ i l * G l j)
        (∑ l, A₁ i l * G l j) (∑ l, Cm i l * G l j)
        (∑ l, B₀ i l * G l j) (∑ l, B₁ i l * G l j) *
      L.wordT (C.word j) := by
  classical
  have h := L.codePair_mul C R.word C.word
    (fun i l ↦ L.pencilEntry (k := k) (A₀ i l) (A₁ i l) (Cm i l)
      (B₀ i l) (B₁ i l))
    (fun l j ↦ algebraMap k A (G l j))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  congr 1
  calc ∑ l, L.pencilEntry (k := k) (A₀ i l) (A₁ i l) (Cm i l)
        (B₀ i l) (B₁ i l) * algebraMap k A (G l j)
      = ∑ l, L.pencilEntry (k := k) (A₀ i l * G l j)
          (A₁ i l * G l j) (Cm i l * G l j) (B₀ i l * G l j)
          (B₁ i l * G l j) :=
        Finset.sum_congr rfl fun l _ ↦
          L.pencilEntry_mul_algebraMap _ _ _ _ _ _
    _ = _ := L.sum_pencilEntry Finset.univ _ _ _ _ _

omit [DecidableEq κ] in
/-- **Left scalar move**: multiplying on the left multiplies the five
coefficient matrices on the left. -/
theorem codeScalar_mul_pencilVal
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (G : Matrix ι ι k) :
    L.codeScalar (k := k) R G *
      (∑ i, ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
          (B₁ i j) * L.wordT (C.word j)) =
    ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (∑ l, G i l * A₀ l j)
        (∑ l, G i l * A₁ l j) (∑ l, G i l * Cm l j)
        (∑ l, G i l * B₀ l j) (∑ l, G i l * B₁ l j) *
      L.wordT (C.word j) := by
  classical
  have h := L.codePair_mul R R.word C.word
    (fun i l ↦ algebraMap k A (G i l))
    (fun l j ↦ L.pencilEntry (k := k) (A₀ l j) (A₁ l j) (Cm l j)
      (B₀ l j) (B₁ l j))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  congr 1
  calc ∑ l, algebraMap k A (G i l) *
        L.pencilEntry (k := k) (A₀ l j) (A₁ l j) (Cm l j) (B₀ l j)
          (B₁ l j)
      = ∑ l, L.pencilEntry (k := k) (G i l * A₀ l j)
          (G i l * A₁ l j) (G i l * Cm l j) (G i l * B₀ l j)
          (G i l * B₁ l j) :=
        Finset.sum_congr rfl fun l _ ↦
          L.algebraMap_mul_pencilEntry _ _ _ _ _ _
    _ = _ := L.sum_pencilEntry Finset.univ _ _ _ _ _

end LeavittFamily
end NonsoficGroupsExist
