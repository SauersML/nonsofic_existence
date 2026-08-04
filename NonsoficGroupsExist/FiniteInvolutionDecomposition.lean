import NonsoficGroupsExist.InvolutionSplitting
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite simultaneous splitting by involutions

This file iterates the explicit two-way involution splitting over a finite
family.  Summing all binary components recovers the original vector, and the
sum of their squared norms is exactly the original squared norm.  The proof is
a finite induction and therefore applies in arbitrary real Hilbert spaces;
it does not appeal to a projection-valued measure or a finite-dimensional
spectral theorem.
-/

namespace NonsoficGroupsExist

universe u v

namespace FiniteInvolutionDecomposition

open InvolutionSplitting

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component selected by a binary sign assignment for a finite family
of represented group elements.  `true` selects the `+1` piece. -/
noncomputable def iteratedPart (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    {n : ℕ} → (Fin n → G) → (Fin n → Bool) → E → E
  | 0, _, _, z => z
  | n + 1, c, sign, z =>
      let tail := iteratedPart rho
        (fun i : Fin n ↦ c i.succ) (fun i : Fin n ↦ sign i.succ) z
      if sign 0 then positivePart rho (c 0) tail
      else negativePart rho (c 0) tail

/-- The binary components sum to the original vector. -/
theorem sum_iteratedPart (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (n : ℕ) (c : Fin n → G) (z : E) :
    ∑ sign : Fin n → Bool, iteratedPart rho c sign z = z := by
  induction n generalizing z with
  | zero => simp [iteratedPart]
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)
      let tail : Fin n → G := fun i ↦ c i.succ
      calc
        ∑ sign : Fin (n + 1) → Bool, iteratedPart rho c sign z =
            ∑ p : Bool × (Fin n → Bool), iteratedPart rho c (e p) z := by
          exact (Equiv.sum_comp e fun sign ↦ iteratedPart rho c sign z).symm
        _ = ∑ sign : Fin n → Bool, iteratedPart rho tail sign z := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sign _
          simp [iteratedPart, e, tail]
          let w := iteratedPart rho tail sign z
          change positivePart rho (c 0) w + negativePart rho (c 0) w = w
          exact positivePart_add_negativePart rho (c 0) w
        _ = z := ih tail z

/-- If every represented element is an involution, the squared norms of all
binary components sum exactly to the squared norm of the original vector. -/
theorem sum_norm_iteratedPart_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (n : ℕ) (c : Fin n → G) (hc : ∀ i, c i ^ 2 = 1) (z : E) :
    ∑ sign : Fin n → Bool, ‖iteratedPart rho c sign z‖ ^ 2 = ‖z‖ ^ 2 := by
  induction n generalizing z with
  | zero => simp [iteratedPart]
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)
      let tail : Fin n → G := fun i ↦ c i.succ
      have htail : ∀ i, tail i ^ 2 = 1 := fun i ↦ hc i.succ
      calc
        ∑ sign : Fin (n + 1) → Bool, ‖iteratedPart rho c sign z‖ ^ 2 =
            ∑ p : Bool × (Fin n → Bool),
              ‖iteratedPart rho c (e p) z‖ ^ 2 := by
          exact (Equiv.sum_comp e fun sign ↦
            ‖iteratedPart rho c sign z‖ ^ 2).symm
        _ = ∑ sign : Fin n → Bool,
            ‖iteratedPart rho tail sign z‖ ^ 2 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sign _
          simpa [iteratedPart, e, tail, add_comm] using
            norm_positivePart_sq_add_norm_negativePart_sq rho (hc 0)
              (iteratedPart rho tail sign z)
        _ = ‖z‖ ^ 2 := ih tail htail z

/-- For a commuting family of involutions, every binary component is a
simultaneous `+1`/`-1` eigenvector with the prescribed signs. -/
theorem action_iteratedPart
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    (sign : Fin n → Bool) (z : E) (i : Fin n) :
    rho (c i) (iteratedPart rho c sign z) =
      if sign i then iteratedPart rho c sign z
      else -iteratedPart rho c sign z := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [iteratedPart]
        split <;> simp_all [action_positivePart, action_negativePart]
      · let tail : Fin n → G := fun t ↦ c t.succ
        let tailSign : Fin n → Bool := fun t ↦ sign t.succ
        let w := iteratedPart rho tail tailSign z
        have htailExp : ∀ t, tail t ^ 2 = 1 := fun t ↦ hc t.succ
        have htailComm : Pairwise (Function.onFun Commute tail) := by
          intro a b hab
          apply hcomm
          intro hs
          exact hab (Fin.succ_inj.mp hs)
        have htailAction := ih tail htailExp htailComm tailSign j
        have hj0 : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
        have hdc : Commute (c j.succ) (c 0) := hcomm hj0
        change rho (c j.succ)
            (if sign 0 then positivePart rho (c 0) w
              else negativePart rho (c 0) w) =
          if sign j.succ then
            (if sign 0 then positivePart rho (c 0) w
              else negativePart rho (c 0) w)
          else -(if sign 0 then positivePart rho (c 0) w
              else negativePart rho (c 0) w)
        split <;> simp only
          [action_positivePart_of_commute rho hdc,
            action_negativePart_of_commute rho hdc]
        all_goals
          rw [htailAction]
          split <;> try rfl
          simp only [positivePart_neg, negativePart_neg]
          rfl

end FiniteInvolutionDecomposition

end NonsoficGroupsExist
