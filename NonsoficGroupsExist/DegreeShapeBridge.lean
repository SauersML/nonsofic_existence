import NonsoficGroupsExist.ShapeCalculus
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# From degree windows to rectangular shapes

Pure-degree spans sit inside shape spans at every sufficiently deep
interface: a monomial `s_a t_b` of degree `d` padded by `r` trailing
cylinders lives in shape `(|a| + r, |b| + r)`, and interfaces can be
chosen uniformly across a finite family.  Together with the matrix
rank bounds this converts homogeneous element identities into
rectangular matrix identities where composites through low interfaces
have provably small rank.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [CommRing k] [Algebra k A]

/-- Every list is `List.ofFn` of its own entries. -/
theorem exists_ofFn_eq (a : List (Fin 2)) :
    ∃ f : Fin a.length → Fin 2, List.ofFn f = a :=
  ⟨a.get, List.ofFn_get a⟩

/-- A monomial lies in every shape span obtained by padding both
words by a common depth. -/
theorem monomial_mem_shapeSpan (a b : List (Fin 2)) (r : ℕ) :
    L.wordS a * L.wordT b ∈ Submodule.span k
      (L.shapeMonomials (a.length + r) (b.length + r)) := by
  induction r with
  | zero =>
      obtain ⟨f, hf⟩ := exists_ofFn_eq a
      obtain ⟨g, hg⟩ := exists_ofFn_eq b
      exact Submodule.subset_span ⟨f, g, by rw [hf, hg]⟩
  | succ r ih =>
      exact L.span_shapeMonomials_le_succ (a.length + r)
        (b.length + r) ih

/-- **Degree spans embed in shape spans**: an element of pure degree
`d` lies in the shape span `(p, q)` for every deep enough interface
`q` with `(p : ℤ) = q + d`. -/
theorem exists_shapeSpan_of_degreeSpan {d : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials d d)) :
    ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q → (p : ℤ) = (q : ℤ) + d →
      x ∈ Submodule.span k (L.shapeMonomials p q) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine ⟨b.length, fun p q hq hpq ↦ ?_⟩
      have hd : (a.length : ℤ) - b.length = d := le_antisymm hh hl
      have h := L.monomial_mem_shapeSpan (k := k) a b (q - b.length)
      have hp : a.length + (q - b.length) = p := by omega
      have hq2 : b.length + (q - b.length) = q := by omega
      rw [hp, hq2] at h
      exact h
  | zero => exact ⟨0, fun p q _ _ ↦ Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨nx, hnx⟩ := hx
      obtain ⟨ny, hny⟩ := hy
      exact ⟨max nx ny, fun p q hq hpq ↦ Submodule.add_mem _
        (hnx p q (le_trans (le_max_left _ _) hq) hpq)
        (hny p q (le_trans (le_max_right _ _) hq) hpq)⟩
  | smul r x _ hx =>
      obtain ⟨nx, hnx⟩ := hx
      exact ⟨nx, fun p q hq hpq ↦
        Submodule.smul_mem _ r (hnx p q hq hpq)⟩

/-- Sums of representing matrices represent sums. -/
theorem shapeRep_add {p q : ℕ}
    {M N : Matrix (Fin p → Fin 2) (Fin q → Fin 2) k} {x y : A}
    (hM : L.ShapeRep p q M x) (hN : L.ShapeRep p q N y) :
    L.ShapeRep p q (M + N) (x + y) := by
  unfold ShapeRep at hM hN ⊢
  rw [hM, hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  rw [Matrix.add_apply, add_smul]

/-- Finite sums of representing matrices represent finite sums. -/
theorem shapeRep_finsetSum {p q : ℕ} {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Fin p → Fin 2) (Fin q → Fin 2) k) (x : ι → A)
    (h : ∀ i ∈ s, L.ShapeRep p q (M i) (x i)) :
    L.ShapeRep p q (∑ i ∈ s, M i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold ShapeRep
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact L.shapeRep_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end LeavittFamily

/-- Sum of finitely many matrices has rank at most the sum of the
ranks. -/
theorem rank_finsetSum_le {m n R : Type*} [Fintype n] [Field R]
    {ι : Type*} (s : Finset ι) (M : ι → Matrix m n R) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (Matrix.rank_add_le _ _) (by omega)

end NonsoficGroupsExist
