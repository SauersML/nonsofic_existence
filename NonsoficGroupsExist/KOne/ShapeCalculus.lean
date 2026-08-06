import NonsoficGroupsExist.Leavitt.LeavittDegreeZero
import Mathlib.Data.Matrix.Basic

/-!
# The rectangular shape calculus

Homogeneous elements of a binary Leavitt family have canonical
rectangular matrix representations: an element of the span of the
shape-`(p, q)` monomials `s_γ t_δ` (`|γ| = p`, `|δ| = q`) is
`Σ M γ δ • s_γ t_δ` for a unique scalar matrix `M`, entries are
recovered by compression `t_γ · x · s_δ`, and the assignment is
multiplicative: at matching interfaces the representing matrix of a
product is the product of the representing matrices, while the unit
`1` is represented by the identity matrix at every square shape.
This is the engine behind the rank arguments of the `K₁` computation:
degree-`d` elements are `2^{n+d} × 2^n`-shaped, so composites through
low levels have small rank.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The monomials of shape `(p, q)`: `s`-word of length `p`, `t`-word
of length `q`. -/
def shapeMonomials (p q : ℕ) : Set A :=
  {x | ∃ (f : Fin p → Fin 2) (g : Fin q → Fin 2),
    x = L.wordS (List.ofFn f) * L.wordT (List.ofFn g)}

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- An element is *shape-represented* by a scalar matrix when it is
the corresponding combination of shape monomials. -/
def ShapeRep (p q : ℕ) (M : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k)
    (x : A) : Prop :=
  x = ∑ γ : Fin p → Fin 2, ∑ δ : Fin q → Fin 2,
    M γ δ • (L.wordS (List.ofFn γ) * L.wordT (List.ofFn δ))

theorem shapeRep_mem_span {p q : ℕ}
    {M : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k} {x : A}
    (h : L.ShapeRep p q M x) :
    x ∈ Submodule.span k (L.shapeMonomials p q) := by
  rw [h]
  refine Submodule.sum_mem _ fun γ _ ↦ Submodule.sum_mem _ fun δ _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, δ, rfl⟩)

/-- Every element of the shape span has a representing matrix. -/
theorem exists_shapeRep {p q : ℕ} {x : A}
    (hx : x ∈ Submodule.span k (L.shapeMonomials p q)) :
    ∃ M : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k,
      L.ShapeRep p q M x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨f, g, rfl⟩ := hxmem
      refine ⟨Matrix.single f g 1, ?_⟩
      unfold ShapeRep
      rw [Finset.sum_eq_single f, Finset.sum_eq_single g]
      · simp [Matrix.single]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hg
        exact absurd (Finset.mem_univ g) hg
      · intro b _ hb
        refine Finset.sum_eq_zero fun δ _ ↦ ?_
        simp [Ne.symm hb]
      · intro hf
        exact absurd (Finset.mem_univ f) hf
  | zero => exact ⟨0, by simp [ShapeRep]⟩
  | add x y _ _ hx hy =>
      obtain ⟨M, hM⟩ := hx
      obtain ⟨N, hN⟩ := hy
      refine ⟨M + N, ?_⟩
      unfold ShapeRep at hM hN ⊢
      rw [hM, hN, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      rw [Matrix.add_apply, add_smul]
  | smul r x _ hx =>
      obtain ⟨M, hM⟩ := hx
      refine ⟨r • M, ?_⟩
      unfold ShapeRep at hM ⊢
      rw [hM, Finset.smul_sum]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      rw [Matrix.smul_apply, smul_smul, smul_eq_mul]

/-- Entry extraction: compressing a represented element between
equal-length words recovers the matrix entry. -/
theorem shapeRep_entry {p q : ℕ}
    {M : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k} {x : A}
    (h : L.ShapeRep p q M x) (γ : Fin p → Fin 2) (δ : Fin q → Fin 2) :
    L.wordT (List.ofFn γ) * x * L.wordS (List.ofFn δ) =
      algebraMap k A (M γ δ) := by
  classical
  have horthP : ∀ a b : Fin p → Fin 2,
      L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
        if a = b then 1 else 0 :=
    fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode p) a b
  have horthQ : ∀ a b : Fin q → Fin 2,
      L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
        if a = b then 1 else 0 :=
    fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode q) a b
  have hterm : ∀ (a : Fin p → Fin 2) (b : Fin q → Fin 2),
      L.wordT (List.ofFn γ) *
        (M a b • (L.wordS (List.ofFn a) * L.wordT (List.ofFn b))) *
        L.wordS (List.ofFn δ) =
      M a b • ((L.wordT (List.ofFn γ) * L.wordS (List.ofFn a)) *
        (L.wordT (List.ofFn b) * L.wordS (List.ofFn δ))) := by
    intro a b
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    noncomm_ring
  calc L.wordT (List.ofFn γ) * x * L.wordS (List.ofFn δ)
      = ∑ a : Fin p → Fin 2, ∑ b : Fin q → Fin 2,
          L.wordT (List.ofFn γ) *
            (M a b • (L.wordS (List.ofFn a) * L.wordT (List.ofFn b))) *
            L.wordS (List.ofFn δ) := by
        rw [h, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a : Fin p → Fin 2, ∑ b : Fin q → Fin 2,
          M a b • (((if γ = a then (1 : A) else 0)) *
            (if b = δ then (1 : A) else 0)) := by
        refine Finset.sum_congr rfl fun a _ ↦
          Finset.sum_congr rfl fun b _ ↦ ?_
        rw [hterm a b, horthP γ a, horthQ b δ]
    _ = algebraMap k A (M γ δ) := by
        rw [Finset.sum_eq_single γ, Finset.sum_eq_single δ]
        · simp [Algebra.smul_def]
        · intro b _ hb
          simp [if_neg hb]
        · intro hδ
          exact absurd (Finset.mem_univ δ) hδ
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ ↦ ?_
          simp [if_neg (Ne.symm ha)]
        · intro hγ
          exact absurd (Finset.mem_univ γ) hγ

/-- Uniqueness of the representing matrix, given that scalars embed. -/
theorem shapeRep_unique {p q : ℕ}
    (hinj : Function.Injective (algebraMap k A))
    {M N : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k} {x : A}
    (hM : L.ShapeRep p q M x) (hN : L.ShapeRep p q N x) : M = N := by
  funext γ δ
  refine hinj ?_
  rw [← L.shapeRep_entry hM γ δ, ← L.shapeRep_entry hN γ δ]

/-- The unit is represented by the identity matrix at every square
shape. -/
theorem shapeRep_one (n : ℕ) : L.ShapeRep n n (1 : Matrix _ _ k) 1 := by
  classical
  unfold ShapeRep
  have hcomplete := L.fullBinaryCode_complete n
  unfold IsComplete fullBinaryCode at hcomplete
  rw [← hcomplete]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [Finset.sum_eq_single γ]
  · rw [Matrix.one_apply_eq, one_smul, cylinder]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  · intro hγ
    exact absurd (Finset.mem_univ γ) hγ

/-- Multiplicativity at matching interfaces: representing matrices of
composable elements multiply. -/
theorem shapeRep_mul {p q r : ℕ}
    {M : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k}
    {N : Matrix (Fin q → Fin 2) (Fin r → Fin 2) k} {x y : A}
    (hM : L.ShapeRep p q M x) (hN : L.ShapeRep q r N y) :
    L.ShapeRep p r (M * N) (x * y) := by
  classical
  have horthQ : ∀ a b : Fin q → Fin 2,
      L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
        if a = b then 1 else 0 :=
    fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode q) a b
  unfold ShapeRep at hM hN ⊢
  rw [hM, hN, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [Finset.sum_mul]
  calc ∑ δ : Fin q → Fin 2,
        (M γ δ • (L.wordS (List.ofFn γ) * L.wordT (List.ofFn δ))) *
        ∑ δ' : Fin q → Fin 2, ∑ ε : Fin r → Fin 2,
          N δ' ε • (L.wordS (List.ofFn δ') * L.wordT (List.ofFn ε))
      = ∑ δ : Fin q → Fin 2, ∑ δ' : Fin q → Fin 2,
          ∑ ε : Fin r → Fin 2, (M γ δ * N δ' ε) •
            (L.wordS (List.ofFn γ) *
              (L.wordT (List.ofFn δ) * L.wordS (List.ofFn δ')) *
              L.wordT (List.ofFn ε)) := by
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ' _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        noncomm_ring
    _ = ∑ δ : Fin q → Fin 2, ∑ ε : Fin r → Fin 2,
          (M γ δ * N δ ε) •
            (L.wordS (List.ofFn γ) * L.wordT (List.ofFn ε)) := by
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [Finset.sum_eq_single δ]
        · rw [horthQ δ δ, if_pos rfl, mul_one]
        · intro δ' _ hδ'
          rw [horthQ δ δ', if_neg (Ne.symm hδ')]
          rw [show L.wordS (List.ofFn γ) * (0 : A) *
            L.wordT (List.ofFn ε) = 0 from by noncomm_ring, smul_zero]
        · intro hδ
          exact absurd (Finset.mem_univ δ) hδ
    _ = ∑ ε : Fin r → Fin 2, (M * N) γ ε •
          (L.wordS (List.ofFn γ) * L.wordT (List.ofFn ε)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [Matrix.mul_apply, Finset.sum_smul]

end Scalars

section Padding

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Shape spans pad: splitting the trailing cylinder rewrites a
shape-`(p, q)` monomial as a sum of shape-`(p+1, q+1)` monomials. -/
theorem span_shapeMonomials_le_succ (p q : ℕ) :
    Submodule.span k (L.shapeMonomials p q) ≤
      Submodule.span k (L.shapeMonomials (p + 1) (q + 1)) := by
  rw [Submodule.span_le]
  rintro x ⟨f, g, rfl⟩
  have hsplit : L.wordS (List.ofFn f) * L.wordT (List.ofFn g) =
      ∑ i : Fin 2, L.wordS (List.ofFn f ++ [i]) *
        L.wordT (List.ofFn g ++ [i]) := by
    have h1 : L.wordS (List.ofFn f) * L.wordT (List.ofFn g) =
        L.wordS (List.ofFn f) * (L.s 0 * L.t 0 + L.s 1 * L.t 1) *
          L.wordT (List.ofFn g) := by
      rw [L.sum_s_mul_t, mul_one]
    rw [h1, Fin.sum_univ_two]
    simp only [wordS_append, wordT_append, wordS_cons, wordT_cons,
      wordS_nil, wordT_nil]
    noncomm_ring
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ?_
  refine ⟨Fin.snoc f i, Fin.snoc g i, ?_⟩
  have hsnoc : ∀ (m : ℕ) (h : Fin m → Fin 2),
      List.ofFn (Fin.snoc h i) = List.ofFn h ++ [i] := by
    intro m h
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  rw [hsnoc p f, hsnoc q g]

end Padding

end LeavittFamily
end NonsoficGroupsExist

