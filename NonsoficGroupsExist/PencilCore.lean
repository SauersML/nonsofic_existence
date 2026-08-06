import NonsoficGroupsExist.IncomparableUnipotents
import NonsoficGroupsExist.BalancedStableRank
import NonsoficGroupsExist.LeavittBalancedUnits

/-!
# Pencil core: the two move generators land in the class group

The pencil elimination manipulates a narrow unit through the depth-`n`
matrix picture `M_{2ⁿ}(A) ≅ A` (`prefixRingEquiv` over the full binary
code).  Only two kinds of multipliers are used, and both transport into
the diagonal class group:

* scalar matrices — their images are balanced values at depth `n`
  (`balancedEmbed`), hence in `H` whenever they are units;
* block unipotents `1 + N` with `N` supported on `S × T` for disjoint
  row/column index sets — their images are products of incomparable
  unipotents, because every cross term dies on the orthogonality
  `t_j s_i = 0` of distinct depth-`n` words.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- **Scalar-matrix moves are in `H`**: a unit whose value is the
depth-`n` embedding of a scalar matrix lies in the class group. -/
theorem balancedEmbed_unit_mem_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (n : ℕ)
    (G : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) (u : Aˣ)
    (hu : (u : A) = L.balancedEmbed (k := k) n G) :
    u ∈ stableUnits A :=
  L.mem_stableUnits_of_val_mem_levelSpan hdiv n u
    (by rw [hu]; exact L.balancedEmbed_mem_span (k := k) n G)

/-- **Block-unipotent moves are in `H`**: a unit of value
`1 + Σ_{(i,j) ∈ S × T} s_i · N i j · t_j` with `S`, `T` disjoint sets
of depth-`n` words is a product of incomparable unipotents. -/
theorem sum_incomparable_unipotent_mem {n : ℕ}
    {S T : Finset (Fin n → Fin 2)} (hST : Disjoint S T)
    (N : (Fin n → Fin 2) → (Fin n → Fin 2) → A) (u : Aˣ)
    (hu : (u : A) = 1 + ∑ p ∈ S ×ˢ T,
      L.wordS (List.ofFn p.1) * N p.1 p.2 * L.wordT (List.ofFn p.2)) :
    u ∈ stableUnits A := by
  classical
  suffices h : ∀ P : Finset ((Fin n → Fin 2) × (Fin n → Fin 2)),
      P ⊆ S ×ˢ T → ∀ u : Aˣ,
      (u : A) = 1 + ∑ p ∈ P,
        L.wordS (List.ofFn p.1) * N p.1 p.2 * L.wordT (List.ofFn p.2) →
      u ∈ stableUnits A from h _ subset_rfl u hu
  intro P
  induction P using Finset.cons_induction with
  | empty =>
      intro _ u hu
      have hone : u = 1 := Units.ext (by rw [Units.val_one]; simpa using hu)
      rw [hone]
      exact one_mem _
  | cons p P hp ih =>
      intro hPsub u hu
      have hpST : p ∈ S ×ˢ T := hPsub (Finset.mem_cons.mpr (Or.inl rfl))
      have hp1S : p.1 ∈ S := (Finset.mem_product.mp hpST).1
      have hp2T : p.2 ∈ T := (Finset.mem_product.mp hpST).2
      have hp12 : p.1 ≠ p.2 := fun h ↦
        (Finset.disjoint_left.mp hST hp1S) (h ▸ hp2T)
      have hinc : ¬List.ofFn p.1 <+: List.ofFn p.2 :=
        (fullBinaryCode n).prefix_free hp12
      have hinc' : ¬List.ofFn p.2 <+: List.ofFn p.1 :=
        (fullBinaryCode n).prefix_free (Ne.symm hp12)
      set ν : Aˣ := L.incomparableUnit hinc hinc' (N p.1 p.2) with hν
      have hνval : (ν : A) = 1 +
          L.wordS (List.ofFn p.1) * N p.1 p.2 * L.wordT (List.ofFn p.2) :=
        rfl
      -- every cross term dies on word orthogonality
      have hcross : (∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
            L.wordT (List.ofFn q.2)) *
          (L.wordS (List.ofFn p.1) * N p.1 p.2 *
            L.wordT (List.ofFn p.2)) = 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero fun q hq ↦ ?_
        have hqST : q ∈ S ×ˢ T := hPsub (Finset.subset_cons hp hq)
        have hq2T : q.2 ∈ T := (Finset.mem_product.mp hqST).2
        have hne : q.2 ≠ p.1 := fun h ↦
          (Finset.disjoint_left.mp hST hp1S) (h ▸ hq2T)
        have horth : L.wordT (List.ofFn q.2) * L.wordS (List.ofFn p.1) =
            0 := by
          have h := L.prefixCode_orthogonal (fullBinaryCode n) q.2 p.1
          rw [if_neg hne] at h
          exact h
        rw [show L.wordS (List.ofFn q.1) * N q.1 q.2 *
            L.wordT (List.ofFn q.2) *
            (L.wordS (List.ofFn p.1) * N p.1 p.2 *
              L.wordT (List.ofFn p.2)) =
          L.wordS (List.ofFn q.1) * N q.1 q.2 *
            (L.wordT (List.ofFn q.2) * L.wordS (List.ofFn p.1)) *
            (N p.1 p.2 * L.wordT (List.ofFn p.2)) from by noncomm_ring,
          horth, mul_zero, zero_mul]
      -- peel the fresh unipotent off the value
      have hval : (1 + ∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
          L.wordT (List.ofFn q.2)) * (ν : A) = (u : A) := by
        rw [hνval, hu, Finset.sum_cons]
        calc (1 + ∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
              L.wordT (List.ofFn q.2)) *
            (1 + L.wordS (List.ofFn p.1) * N p.1 p.2 *
              L.wordT (List.ofFn p.2))
            = 1 + (L.wordS (List.ofFn p.1) * N p.1 p.2 *
                L.wordT (List.ofFn p.2) +
              ∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
                L.wordT (List.ofFn q.2)) +
              (∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
                L.wordT (List.ofFn q.2)) *
              (L.wordS (List.ofFn p.1) * N p.1 p.2 *
                L.wordT (List.ofFn p.2)) := by noncomm_ring
          _ = 1 + (L.wordS (List.ofFn p.1) * N p.1 p.2 *
                L.wordT (List.ofFn p.2) +
              ∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
                L.wordT (List.ofFn q.2)) := by
              rw [hcross, add_zero]
      have hu' : ((u * ν⁻¹ : Aˣ) : A) = 1 +
          ∑ q ∈ P, L.wordS (List.ofFn q.1) * N q.1 q.2 *
            L.wordT (List.ofFn q.2) := by
        rw [Units.val_mul, ← hval, mul_assoc, Units.mul_inv, mul_one]
      have hsplit : u = (u * ν⁻¹) * ν := by group
      rw [hsplit]
      exact mul_mem
        (ih (fun q hq ↦ hPsub (Finset.subset_cons hp hq)) (u * ν⁻¹) hu')
        (L.incomparableUnit_mem hinc hinc' (N p.1 p.2))

/-- Nested-sum form of the block-unipotent membership. -/
theorem sum_incomparable_unipotent_mem' {n : ℕ}
    {S T : Finset (Fin n → Fin 2)} (hST : Disjoint S T)
    (N : (Fin n → Fin 2) → (Fin n → Fin 2) → A) (u : Aˣ)
    (hu : (u : A) = 1 + ∑ i ∈ S, ∑ j ∈ T,
      L.wordS (List.ofFn i) * N i j * L.wordT (List.ofFn j)) :
    u ∈ stableUnits A := by
  refine L.sum_incomparable_unipotent_mem hST N u ?_
  rw [hu, Finset.sum_product]

end LeavittFamily
end NonsoficGroupsExist
