import NonsoficGroupsExist.PrefixCode
import NonsoficGroupsExist.FieldMatrixReduction

/-!
# Degree-zero units of a Leavitt family are central scalars mod the diagonal class

The degree-zero conclusion of the rose-graph `K₁` computation.  The
full binary code at depth `n` identifies the algebra with a `2ⁿ × 2ⁿ`
matrix ring; a unit whose value lies in the span of the balanced
monomials `s_α t_β` (`|α| = |β| = n`) has *scalar* matrix entries under
this identification, because `t_γ s_α` and `t_β s_δ` are `0` or `1` for
equal-length words.  The field-coefficient reduction then places the
unit in `centralClassGroup`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

/-- The full binary prefix code at depth `n`: all `2ⁿ` words. -/
def fullBinaryCode (n : ℕ) : BinaryPrefixCode (Fin n → Fin 2) where
  word f := List.ofFn f
  prefix_free := by
    intro f g hfg hp
    have hlen : (List.ofFn f).length = (List.ofFn g).length := by simp
    exact hfg (List.ofFn_inj.mp (hp.eq_of_length hlen))

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

theorem cylinder_cons (b : Fin 2) (w : List (Fin 2)) :
    L.cylinder (b :: w) = L.s b * L.cylinder w * L.t b := by
  simp [cylinder, mul_assoc]

/-- The full depth-`n` code is complete: the `2ⁿ` cylinders sum
to `1`. -/
theorem fullBinaryCode_complete (n : ℕ) :
    L.IsComplete (fullBinaryCode n) := by
  classical
  induction n with
  | zero =>
      show ∑ f : Fin 0 → Fin 2, L.cylinder (List.ofFn f) = 1
      simp [cylinder]
  | succ n ih =>
      have ih' : ∑ g : Fin n → Fin 2, L.cylinder (List.ofFn g) = 1 := ih
      show ∑ f : Fin (n + 1) → Fin 2, L.cylinder (List.ofFn f) = 1
      have hre : ∑ f : Fin (n + 1) → Fin 2, L.cylinder (List.ofFn f) =
          ∑ p : Fin 2 × (Fin n → Fin 2),
            L.cylinder (List.ofFn (Fin.cons p.1 p.2)) :=
        (Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Fin 2) _ _
          fun p ↦ rfl).symm
      have hofn : ∀ (b : Fin 2) (g : Fin n → Fin 2),
          List.ofFn (Fin.cons b g) = b :: List.ofFn g := by
        intro b g
        rw [List.ofFn_succ]
        simp
      have hbranch : ∀ b : Fin 2,
          (∑ g : Fin n → Fin 2,
            L.s b * L.cylinder (List.ofFn g) * L.t b) = L.s b * L.t b := by
        intro b
        rw [← Finset.sum_mul, ← Finset.mul_sum, ih', mul_one]
      rw [hre, Fintype.sum_prod_type]
      simp_rw [hofn, L.cylinder_cons]
      rw [Fin.sum_univ_two, hbranch 0, hbranch 1]
      exact L.sum_s_mul_t

/-- The balanced (degree-zero) monomials at depth `n`. -/
def levelMonomials (n : ℕ) : Set A :=
  {x | ∃ f g : Fin n → Fin 2,
    x = L.wordS (List.ofFn f) * L.wordT (List.ofFn g)}

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Matrix entries of degree-zero elements are scalars: compressing an
element of the balanced span between equal-length words lands in the
image of the ground ring. -/
theorem entry_mem_range_algebraMap (n : ℕ) {x : A}
    (hx : x ∈ Submodule.span k (L.levelMonomials n))
    (γ δ : Fin n → Fin 2) :
    L.wordT (List.ofFn γ) * x * L.wordS (List.ofFn δ) ∈
      Set.range (algebraMap k A) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨f, g, rfl⟩ := hxmem
      have horth : ∀ a b : Fin n → Fin 2,
          L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
            if a = b then 1 else 0 :=
        fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode n) a b
      rw [show L.wordT (List.ofFn γ) *
          (L.wordS (List.ofFn f) * L.wordT (List.ofFn g)) *
          L.wordS (List.ofFn δ) =
        (L.wordT (List.ofFn γ) * L.wordS (List.ofFn f)) *
          (L.wordT (List.ofFn g) * L.wordS (List.ofFn δ)) from by
            noncomm_ring,
        horth γ f, horth g δ]
      refine ⟨(if γ = f then 1 else 0) * (if g = δ then 1 else 0), ?_⟩
      rw [map_mul]
      congr 1 <;> split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨cx, hcx⟩ := hx
      obtain ⟨cy, hcy⟩ := hy
      exact ⟨cx + cy, by rw [map_add, hcx, hcy]; noncomm_ring⟩
  | smul r x _ hx =>
      obtain ⟨c, hc⟩ := hx
      refine ⟨r * c, ?_⟩
      rw [map_mul, hc, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

end Scalars

section Reduction

open MatrixDiagonalization

variable {k : Type*} [Field k] [Algebra k A]

/-- **Degree-zero scalar reduction**: a unit whose value lies in the
balanced span at some depth is a central scalar modulo the diagonal
class group. -/
theorem mem_centralClassGroup_of_val_mem_levelSpan [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (n : ℕ) (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (L.levelMonomials n)) :
    u ∈ centralClassGroup A := by
  classical
  set F := L.prefixMatrixFamily (fullBinaryCode n)
    (L.fullBinaryCode_complete n) with hF
  have hentry : ∀ γ δ : Fin n → Fin 2, ∃ c : k,
      algebraMap k A c = F.right γ * (u : A) * F.left δ := by
    intro γ δ
    obtain ⟨c, hc⟩ := L.entry_mem_range_algebraMap n hu γ δ
    exact ⟨c, hc⟩
  choose C hC using hentry
  have hU : ((F.unitsEquiv.symm u :
        (Matrix (Fin n → Fin 2) (Fin n → Fin 2) A)ˣ) :
        Matrix (Fin n → Fin 2) (Fin n → Fin 2) A) =
      (algebraMap k A).mapMatrix (Matrix.of C) := by
    have hval : ((F.unitsEquiv.symm u :
          (Matrix (Fin n → Fin 2) (Fin n → Fin 2) A)ˣ) :
          Matrix (Fin n → Fin 2) (Fin n → Fin 2) A) =
        F.matrixRingEquiv.symm ((u : Aˣ) : A) := rfl
    rw [hval]
    ext γ δ
    rw [F.matrixRingEquiv_symm_apply]
    exact (hC γ δ).symm
  have hmem := F.unitsEquiv_field_matrix_mem_centralClassGroup hdiv
    (algebraMap k A) (fun r x ↦ Algebra.commutes r x) (Matrix.of C)
    (F.unitsEquiv.symm u) hU
  rwa [MulEquiv.apply_symm_apply] at hmem

end Reduction

end LeavittFamily
end NonsoficGroupsExist
