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

theorem positivePart_eq_self_of_action_eq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E)
    (h : rho c z = z) :
    positivePart rho c z = z := by
  rw [positivePart, h]
  module

theorem positivePart_eq_zero_of_action_eq_neg
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E)
    (h : rho c z = -z) :
    positivePart rho c z = 0 := by
  rw [positivePart, h]
  module

theorem negativePart_eq_zero_of_action_eq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E)
    (h : rho c z = z) :
    negativePart rho c z = 0 := by
  rw [negativePart, h]
  module

theorem negativePart_eq_self_of_action_eq_neg
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E)
    (h : rho c z = -z) :
    negativePart rho c z = z := by
  rw [negativePart, h]
  module

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

@[simp] theorem iteratedPart_zero
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (sign : Fin n → Bool) :
    iteratedPart rho c sign 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPart, ih]
      split <;> simp [positivePart, negativePart]

theorem iteratedPart_add
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (sign : Fin n → Bool) (z w : E) :
    iteratedPart rho c sign (z + w) =
      iteratedPart rho c sign z + iteratedPart rho c sign w := by
  induction n generalizing z w with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPart, ih]
      split <;> simp only [positivePart, negativePart, map_add]
      all_goals module

/-- Simultaneous sign projection distributes over every finite sum. -/
theorem iteratedPart_finset_sum
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (sign : Fin n → Bool) {ι : Type*} (A : Finset ι) (f : ι → E) :
    iteratedPart rho c sign (∑ a ∈ A, f a) =
      ∑ a ∈ A, iteratedPart rho c sign (f a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        iteratedPart_add, ih]

/-- Applying a simultaneous sign projection to a joint eigenvector either
keeps that vector or kills it, according to whether the selected signs agree
with its eigencharacter. -/
theorem iteratedPart_of_eigenvector
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (n : ℕ) (c : Fin n → G)
    (tau : Fin n → Bool) (z : E)
    (hact : ∀ i, rho (c i) z = if tau i then z else -z)
    (sign : Fin n → Bool) :
    iteratedPart rho c sign z = if sign = tau then z else 0 := by
  induction n with
  | zero =>
      have hst : sign = tau := Subsingleton.elim _ _
      simp [iteratedPart, hst]
  | succ n ih =>
      let tailC : Fin n → G := fun i ↦ c i.succ
      let tailTau : Fin n → Bool := fun i ↦ tau i.succ
      let tailSign : Fin n → Bool := fun i ↦ sign i.succ
      have htailAct : ∀ i, rho (tailC i) z =
          if tailTau i then z else -z := fun i ↦ hact i.succ
      have htail := ih tailC tailTau htailAct tailSign
      simp only [iteratedPart]
      change (if sign 0 then
          positivePart rho (c 0) (iteratedPart rho tailC tailSign z)
        else negativePart rho (c 0) (iteratedPart rho tailC tailSign z)) = _
      rw [htail]
      by_cases htailEq : tailSign = tailTau
      · rw [if_pos htailEq]
        by_cases hzero : sign 0 = tau 0
        · have hfull : sign = tau := by
            funext i
            refine Fin.cases hzero (fun j ↦ ?_) i
            exact congrFun htailEq j
          rw [if_pos hfull]
          cases hs : sign 0 <;> cases ht : tau 0
          · simpa using negativePart_eq_self_of_action_eq_neg rho (c 0) z
              (by simpa [ht] using hact 0)
          · simp [hs, ht] at hzero
          · simp [hs, ht] at hzero
          · simpa using positivePart_eq_self_of_action_eq rho (c 0) z
              (by simpa [ht] using hact 0)
        · have hfull : sign ≠ tau := by
            intro h
            exact hzero (congrFun h 0)
          rw [if_neg hfull]
          cases hs : sign 0 <;> cases ht : tau 0
          · exact False.elim (hzero (by simp [hs, ht]))
          · simpa using negativePart_eq_zero_of_action_eq rho (c 0) z
              (by simpa [ht] using hact 0)
          · simpa using positivePart_eq_zero_of_action_eq_neg rho (c 0) z
              (by simpa [ht] using hact 0)
          · exact False.elim (hzero (by simp [hs, ht]))
      · rw [if_neg htailEq]
        have hfull : sign ≠ tau := by
          intro h
          apply htailEq
          funext i
          exact congrFun h i.succ
        rw [if_neg hfull]
        split <;> simp [positivePart, negativePart]

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

/-- A coarse simultaneous projection applied to one fine component keeps it
exactly when the coarse signs are the restriction of the fine signs. -/
theorem iteratedPart_coarse_on_fine
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (m n : ℕ) (fine : Fin m → G) (coarse : Fin n → G)
    (index : Fin n → Fin m)
    (hindex : ∀ i, coarse i = fine (index i))
    (hfineSq : ∀ i, fine i ^ 2 = 1)
    (hfineComm : Pairwise (Function.onFun Commute fine))
    (fineSign : Fin m → Bool) (coarseSign : Fin n → Bool) (z : E) :
    iteratedPart rho coarse coarseSign
        (iteratedPart rho fine fineSign z) =
      if coarseSign = fun i ↦ fineSign (index i) then
        iteratedPart rho fine fineSign z
      else 0 := by
  apply iteratedPart_of_eigenvector
  intro i
  rw [hindex i]
  exact action_iteratedPart rho m fine hfineSq hfineComm fineSign z (index i)

/-- Every coarse component is the exact sum of all fine components whose
signs restrict to the coarse sign assignment. -/
theorem iteratedPart_eq_sum_fine_extensions
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (m n : ℕ) (fine : Fin m → G) (coarse : Fin n → G)
    (index : Fin n → Fin m)
    (hindex : ∀ i, coarse i = fine (index i))
    (hfineSq : ∀ i, fine i ^ 2 = 1)
    (hfineComm : Pairwise (Function.onFun Commute fine))
    (coarseSign : Fin n → Bool) (z : E) :
    iteratedPart rho coarse coarseSign z =
      ∑ fineSign ∈ (Finset.univ.filter fun fineSign : Fin m → Bool ↦
          coarseSign = fun i ↦ fineSign (index i)),
        iteratedPart rho fine fineSign z := by
  classical
  calc
    iteratedPart rho coarse coarseSign z =
        iteratedPart rho coarse coarseSign
          (∑ fineSign, iteratedPart rho fine fineSign z) := by
      rw [sum_iteratedPart]
    _ = ∑ fineSign,
        iteratedPart rho coarse coarseSign
          (iteratedPart rho fine fineSign z) := by
      simpa using iteratedPart_finset_sum rho n coarse coarseSign
        (Finset.univ : Finset (Fin m → Bool))
        (fun fineSign ↦ iteratedPart rho fine fineSign z)
    _ = ∑ fineSign,
        if coarseSign = fun i ↦ fineSign (index i) then
          iteratedPart rho fine fineSign z
        else 0 := by
      apply Finset.sum_congr rfl
      intro fineSign _
      exact iteratedPart_coarse_on_fine rho m n fine coarse index hindex
        hfineSq hfineComm fineSign coarseSign z
    _ = ∑ fineSign ∈ (Finset.univ.filter fun fineSign : Fin m → Bool ↦
          coarseSign = fun i ↦ fineSign (index i)),
        iteratedPart rho fine fineSign z := by
      rw [Finset.sum_filter]

/-- Fine sign assignments extending one prescribed coarse sign assignment. -/
def fineExtensionSignSet (m n : ℕ) (index : Fin n → Fin m)
    (coarseSign : Fin n → Bool) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun fineSign ↦
    coarseSign = fun i ↦ fineSign (index i)

/-- Fine sign assignments whose restriction belongs to a selected set of
coarse sign assignments. -/
def fineRestrictionSignSet (m n : ℕ) (index : Fin n → Fin m)
    (coarseSigns : Finset (Fin n → Bool)) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun fineSign ↦
    (fun i ↦ fineSign (index i)) ∈ coarseSigns

theorem fineExtensionSignSet_pairwise_disjoint
    (m n : ℕ) (index : Fin n → Fin m) :
    Pairwise (fun s t : Fin n → Bool ↦
      Disjoint (fineExtensionSignSet m n index s)
        (fineExtensionSignSet m n index t)) := by
  intro s t hst
  rw [Finset.disjoint_left]
  intro fineSign hs ht
  simp only [fineExtensionSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs ht
  exact hst (hs.trans ht.symm)

theorem biUnion_fineExtensionSignSet
    (m n : ℕ) (index : Fin n → Fin m)
    (coarseSigns : Finset (Fin n → Bool)) :
    coarseSigns.biUnion (fineExtensionSignSet m n index) =
      fineRestrictionSignSet m n index coarseSigns := by
  ext fineSign
  simp only [Finset.mem_biUnion, fineExtensionSignSet,
    fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨coarseSign, hcoarse, hrestrict⟩
    exact hrestrict.symm ▸ hcoarse
  · intro hrestrict
    exact ⟨fun i ↦ fineSign (index i), hrestrict, rfl⟩

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

/-- Pythagoras for one coarse component refined into all of its compatible
fine components. -/
theorem norm_iteratedPart_sq_eq_sum_fine_extensions
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (m n : ℕ) (fine : Fin m → G) (coarse : Fin n → G)
    (index : Fin n → Fin m)
    (hindex : ∀ i, coarse i = fine (index i))
    (hfineSq : ∀ i, fine i ^ 2 = 1)
    (hfineComm : Pairwise (Function.onFun Commute fine))
    (coarseSign : Fin n → Bool) (z : E) :
    ‖iteratedPart rho coarse coarseSign z‖ ^ 2 =
      ∑ fineSign ∈ fineExtensionSignSet m n index coarseSign,
        ‖iteratedPart rho fine fineSign z‖ ^ 2 := by
  rw [iteratedPart_eq_sum_fine_extensions rho m n fine coarse index hindex
    hfineSq hfineComm coarseSign z]
  exact norm_sum_iteratedPart_sq rho m fine hfineSq hfineComm
    (fineExtensionSignSet m n index coarseSign) z

/-- Exact conservation of squared Fourier mass across a finite refinement:
fine characters whose restriction lies in a coarse sign set carry exactly the
mass of that coarse sign set. -/
theorem sum_norm_fineRestrictionSignSet_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (m n : ℕ) (fine : Fin m → G) (coarse : Fin n → G)
    (index : Fin n → Fin m)
    (hindex : ∀ i, coarse i = fine (index i))
    (hfineSq : ∀ i, fine i ^ 2 = 1)
    (hfineComm : Pairwise (Function.onFun Commute fine))
    (coarseSigns : Finset (Fin n → Bool)) (z : E) :
    ∑ fineSign ∈ fineRestrictionSignSet m n index coarseSigns,
        ‖iteratedPart rho fine fineSign z‖ ^ 2 =
      ∑ coarseSign ∈ coarseSigns,
        ‖iteratedPart rho coarse coarseSign z‖ ^ 2 := by
  classical
  symm
  calc
    ∑ coarseSign ∈ coarseSigns,
        ‖iteratedPart rho coarse coarseSign z‖ ^ 2 =
        ∑ coarseSign ∈ coarseSigns,
          ∑ fineSign ∈ fineExtensionSignSet m n index coarseSign,
            ‖iteratedPart rho fine fineSign z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro coarseSign _
      exact norm_iteratedPart_sq_eq_sum_fine_extensions rho m n fine coarse
        index hindex hfineSq hfineComm coarseSign z
    _ = ∑ fineSign ∈
          coarseSigns.biUnion (fineExtensionSignSet m n index),
          ‖iteratedPart rho fine fineSign z‖ ^ 2 := by
      have hpair : (coarseSigns : Set (Fin n → Bool)).PairwiseDisjoint
          (fineExtensionSignSet m n index) := by
        intro s _ t _ hst
        exact fineExtensionSignSet_pairwise_disjoint m n index hst
      exact (Finset.sum_biUnion hpair).symm
    _ = ∑ fineSign ∈ fineRestrictionSignSet m n index coarseSigns,
          ‖iteratedPart rho fine fineSign z‖ ^ 2 := by
      rw [biUnion_fineExtensionSignSet]

/-- Conjugating an entire finite family by an involution and simultaneously
acting on the vector preserves the squared norm of each sign component. -/
theorem norm_iteratedPart_conjugated_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (hg : g ^ 2 = 1)
    (n : ℕ) (coarse : Fin n → G) (coarseSign : Fin n → Bool) (z : E) :
    ‖iteratedPart rho (fun i ↦ g * coarse i * g⁻¹) coarseSign z‖ ^ 2 =
      ‖iteratedPart rho coarse coarseSign (rho g z)‖ ^ 2 := by
  have hmap := map_iteratedPart rho g n coarse coarseSign (rho g z)
  have htwice : rho g (rho g z) = z := InvolutionSplitting.action_sq rho hg z
  rw [htwice] at hmap
  calc
    ‖iteratedPart rho (fun i ↦ g * coarse i * g⁻¹) coarseSign z‖ ^ 2 =
        ‖rho g (iteratedPart rho coarse coarseSign (rho g z))‖ ^ 2 := by
      rw [hmap]
    _ = ‖iteratedPart rho coarse coarseSign (rho g z)‖ ^ 2 := by
      rw [(rho g).norm_map]

/-- Exact mass transport when the coarse family is included in the fine
family after conjugation by an involution. -/
theorem sum_norm_fineRestriction_conjugated_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (hg : g ^ 2 = 1)
    (m n : ℕ) (fine : Fin m → G) (coarse : Fin n → G)
    (index : Fin n → Fin m)
    (hindex : ∀ i, g * coarse i * g⁻¹ = fine (index i))
    (hfineSq : ∀ i, fine i ^ 2 = 1)
    (hfineComm : Pairwise (Function.onFun Commute fine))
    (coarseSigns : Finset (Fin n → Bool)) (z : E) :
    ∑ fineSign ∈ fineRestrictionSignSet m n index coarseSigns,
        ‖iteratedPart rho fine fineSign z‖ ^ 2 =
      ∑ coarseSign ∈ coarseSigns,
        ‖iteratedPart rho coarse coarseSign (rho g z)‖ ^ 2 := by
  calc
    ∑ fineSign ∈ fineRestrictionSignSet m n index coarseSigns,
        ‖iteratedPart rho fine fineSign z‖ ^ 2 =
        ∑ coarseSign ∈ coarseSigns,
          ‖iteratedPart rho (fun i ↦ g * coarse i * g⁻¹)
            coarseSign z‖ ^ 2 :=
      sum_norm_fineRestrictionSignSet_sq rho m n fine
        (fun i ↦ g * coarse i * g⁻¹) index hindex hfineSq hfineComm
        coarseSigns z
    _ = ∑ coarseSign ∈ coarseSigns,
          ‖iteratedPart rho coarse coarseSign (rho g z)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro coarseSign _
      exact norm_iteratedPart_conjugated_sq rho g hg n coarse coarseSign z

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
