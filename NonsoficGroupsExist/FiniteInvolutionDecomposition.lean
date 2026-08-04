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

/-- Simultaneous finite sign decomposition is covariant under conjugation of
the entire commuting family. -/
theorem map_iteratedPart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (n : ℕ)
    (c : Fin n → G) (sign : Fin n → Bool) (z : E) :
    rho g (iteratedPart rho c sign z) =
      iteratedPart rho (fun i ↦ g * c i * g⁻¹) sign (rho g z) := by
  induction n with
  | zero => simp [iteratedPart]
  | succ n ih =>
      simp only [iteratedPart]
      split
      · rw [map_positivePart]
        congr 1
        exact ih (fun i ↦ c i.succ) (fun i ↦ sign i.succ)
      · rw [map_negativePart]
        congr 1
        exact ih (fun i ↦ c i.succ) (fun i ↦ sign i.succ)

/-- Distinct sign assignments select orthogonal simultaneous components. -/
theorem inner_iteratedPart_eq_zero_of_ne
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    {sign tau : Fin n → Bool} (hne : sign ≠ tau) (z : E) :
    inner ℝ (iteratedPart rho c sign z) (iteratedPart rho c tau z) = 0 := by
  classical
  have hex : ∃ i, sign i ≠ tau i := by
    by_contra hall
    apply hne
    funext i
    exact Classical.byContradiction (fun hi ↦ hall ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  let a := iteratedPart rho c sign z
  let b := iteratedPart rho c tau z
  have ha := action_iteratedPart rho n c hc hcomm sign z i
  have hb := action_iteratedPart rho n c hc hcomm tau z i
  have hiso := (rho (c i)).inner_map_map a b
  change inner ℝ (rho (c i) a) (rho (c i) b) = inner ℝ a b at hiso
  cases hs : sign i <;> cases ht : tau i
  · exact False.elim (hi (by simp [hs, ht]))
  · simp [hs] at ha
    simp [ht] at hb
    rw [ha, hb] at hiso
    simp [a, b] at hiso
    linarith
  · simp [hs] at ha
    simp [ht] at hb
    rw [ha, hb] at hiso
    simp [a, b] at hiso
    linarith
  · exact False.elim (hi (by simp [hs, ht]))

/-- The squared norm of the sum over any finite set of sign components is the
sum of their squared norms. -/
theorem norm_sum_iteratedPart_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    (A : Finset (Fin n → Bool)) (z : E) :
    ‖∑ sign ∈ A, iteratedPart rho c sign z‖ ^ 2 =
      ∑ sign ∈ A, ‖iteratedPart rho c sign z‖ ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert sign A hsign ih =>
      have hinner : inner ℝ (iteratedPart rho c sign z)
          (∑ tau ∈ A, iteratedPart rho c tau z) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro tau htau
        exact inner_iteratedPart_eq_zero_of_ne rho n c hc hcomm
          (sign := sign) (tau := tau)
          (fun heq ↦ hsign (heq.symm ▸ htau)) z
      rw [Finset.sum_insert hsign, Finset.sum_insert hsign]
      calc
        ‖iteratedPart rho c sign z +
            ∑ tau ∈ A, iteratedPart rho c tau z‖ ^ 2 =
            ‖iteratedPart rho c sign z‖ ^ 2 +
              ‖∑ tau ∈ A, iteratedPart rho c tau z‖ ^ 2 := by
          simpa [pow_two] using
            norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
        _ = ‖iteratedPart rho c sign z‖ ^ 2 +
            ∑ tau ∈ A, ‖iteratedPart rho c tau z‖ ^ 2 := by rw [ih]

/-- The negative spectral projection for one family member keeps exactly the
components assigning that member the negative sign. -/
theorem negativePart_iteratedPart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    (sign : Fin n → Bool) (z : E) (i : Fin n) :
    negativePart rho (c i) (iteratedPart rho c sign z) =
      if sign i then 0 else iteratedPart rho c sign z := by
  unfold negativePart
  rw [action_iteratedPart rho n c hc hcomm sign z i]
  split <;> module

/-- The negative part of the original vector is the sum of precisely its
negative sign components for the selected family member. -/
theorem negativePart_eq_sum_false_iteratedPart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    (z : E) (i : Fin n) :
    negativePart rho (c i) z =
      ∑ sign ∈ (Finset.univ.filter fun sign : Fin n → Bool ↦ sign i = false),
        iteratedPart rho c sign z := by
  let part : (Fin n → Bool) → E := fun sign ↦ iteratedPart rho c sign z
  calc
    negativePart rho (c i) z =
        negativePart rho (c i) (∑ sign, part sign) := by
      rw [sum_iteratedPart]
    _ = ∑ sign, negativePart rho (c i) (part sign) := by
      unfold negativePart
      rw [map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    _ = ∑ sign, if sign i then 0 else part sign := by
      apply Finset.sum_congr rfl
      intro sign _
      exact negativePart_iteratedPart rho n c hc hcomm sign z i
    _ = ∑ sign ∈ (Finset.univ.filter fun sign : Fin n → Bool ↦
        sign i = false), part sign := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro sign _
      cases sign i <;> simp

/-- The negative character mass is exactly the squared norm of the negative
spectral projection. -/
theorem norm_negativePart_sq_eq_sum_false
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (hc : ∀ i, c i ^ 2 = 1)
    (hcomm : Pairwise (Function.onFun Commute c))
    (z : E) (i : Fin n) :
    ‖negativePart rho (c i) z‖ ^ 2 =
      ∑ sign ∈ (Finset.univ.filter fun sign : Fin n → Bool ↦ sign i = false),
        ‖iteratedPart rho c sign z‖ ^ 2 := by
  rw [negativePart_eq_sum_false_iteratedPart rho n c hc hcomm z i]
  exact norm_sum_iteratedPart_sq rho n c hc hcomm _ z

end FiniteInvolutionDecomposition

end NonsoficGroupsExist
