import NonsoficGroupsExist.KOne.CodePairTransport
import NonsoficGroupsExist.KOne.CodeChangeGlue
import NonsoficGroupsExist.KOne.WindowProductClosure

/-!
# Reshaping a code pencil

A pencil's codes are disposable: conjugating by the two code-change
units that swap the row code for any other complete code on the same
index type (and likewise for the column code) preserves membership in
the diagonal class group and transports the pencil data verbatim.
Combined with the window bound for pencil values over depth-controlled
codes, this realizes the session-54 exits.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

-- `stableUnits` lives in `MatrixDiagonalization`
open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

-- the statement never mentions `k`, but `codeBijection_mem_stableUnits`
-- in the proof needs it, so it has to be force-included
include k in
/-- **Reshaping**: two pencil units with the same entry matrix over
different complete code pairs (same index types) are equivalent in the
diagonal class group. -/
theorem reshaped_pencil_mem_iff [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (R P : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (hP : L.IsComplete P)
    (C Q : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (hQ : L.IsComplete Q)
    (E : ι → κ → A) (u v : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j,
      L.wordS (R.word i) * E i j * L.wordT (C.word j))
    (hv : (v : A) = ∑ i, ∑ j,
      L.wordS (P.word i) * E i j * L.wordT (Q.word j)) :
    (u ∈ stableUnits A ↔ v ∈ stableUnits A) := by
  classical
  set F : ι → ι → A := fun i i' ↦ if i = i' then 1 else 0 with hFdef
  set G : κ → κ → A := fun j j' ↦ if j = j' then 1 else 0 with hGdef
  have hFF : ∀ i i' : ι, (∑ j, F i j * F j i') =
      if i = i' then (1 : A) else 0 := by
    intro i i'
    rw [Finset.sum_congr rfl (fun j _ ↦
      show F i j * F j i' = if i = j then F j i' else 0 from by
        show (if i = j then (1 : A) else 0) * F j i' = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ i (fun j ↦ F j i'),
      if_pos (Finset.mem_univ i)]
  have hGG : ∀ j j' : κ, (∑ l, G j l * G l j') =
      if j = j' then (1 : A) else 0 := by
    intro j j'
    rw [Finset.sum_congr rfl (fun l _ ↦
      show G j l * G l j' = if j = l then G l j' else 0 from by
        show (if j = l then (1 : A) else 0) * G l j' = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ j (fun l ↦ G l j'),
      if_pos (Finset.mem_univ j)]
  set ω₁ : Aˣ := L.codePairUnit P hP R hR F F hFF hFF with hω₁
  set ω₂ : Aˣ := L.codePairUnit C hC Q hQ G G hGG hGG with hω₂
  -- collapse identities
  have hcollapseL : ∀ (i : ι) (l : κ), (∑ j, F i j * E j l) = E i l := by
    intro i l
    rw [Finset.sum_congr rfl (fun j _ ↦
      show F i j * E j l = if i = j then E j l else 0 from by
        show (if i = j then (1 : A) else 0) * E j l = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ i (fun j ↦ E j l),
      if_pos (Finset.mem_univ i)]
  have hcollapseR : ∀ (i : ι) (l : κ), (∑ j, E i j * G j l) = E i l := by
    intro i l
    rw [Finset.sum_congr rfl (fun j _ ↦
      show E i j * G j l = if j = l then E i j else 0 from by
        show E i j * (if j = l then (1 : A) else 0) = _
        split_ifs <;> simp),
      Finset.sum_ite_eq' Finset.univ l (fun j ↦ E i j),
      if_pos (Finset.mem_univ l)]
  -- the conjugation identity
  have hval : ((ω₁ * u * ω₂ : Aˣ) : A) = (v : A) := by
    rw [Units.val_mul, Units.val_mul, hω₁, L.codePairUnit_val, hu,
      L.codePair_mul R P.word C.word F E]
    simp only [hcollapseL]
    rw [hω₂, L.codePairUnit_val,
      L.codePair_mul C P.word Q.word E G]
    simp only [hcollapseR]
    rw [hv]
  have hveq : v = ω₁ * u * ω₂ := Units.ext hval.symm
  -- membership of the two code changes
  have hω₁single : ((ω₁ : Aˣ) : A) =
      ∑ i, L.wordS (P.word i) * L.wordT (R.word i) := by
    rw [hω₁, L.codePairUnit_val]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_congr rfl (fun j _ ↦
      show L.wordS (P.word i) * F i j * L.wordT (R.word j) =
        if i = j then L.wordS (P.word i) * L.wordT (R.word j)
          else 0 from by
        show L.wordS (P.word i) * (if i = j then (1 : A) else 0) *
          L.wordT (R.word j) = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ i
        (fun j ↦ L.wordS (P.word i) * L.wordT (R.word j)),
      if_pos (Finset.mem_univ i)]
  have hω₂single : ((ω₂ : Aˣ) : A) =
      ∑ j, L.wordS (C.word j) * L.wordT (Q.word j) := by
    rw [hω₂, L.codePairUnit_val]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_congr rfl (fun l _ ↦
      show L.wordS (C.word j) * G j l * L.wordT (Q.word l) =
        if j = l then L.wordS (C.word j) * L.wordT (Q.word l)
          else 0 from by
        show L.wordS (C.word j) * (if j = l then (1 : A) else 0) *
          L.wordT (Q.word l) = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ j
        (fun l ↦ L.wordS (C.word j) * L.wordT (Q.word l)),
      if_pos (Finset.mem_univ j)]
  have hω₁mem : ω₁ ∈ stableUnits A :=
    L.codeBijection_mem_stableUnits (k := k) hdiv P.word R.word
      P.prefix_free hP R.prefix_free hR ω₁ hω₁single
  have hω₂mem : ω₂ ∈ stableUnits A :=
    L.codeBijection_mem_stableUnits (k := k) hdiv C.word Q.word
      C.prefix_free hC Q.prefix_free hQ ω₂ hω₂single
  constructor
  · intro h
    rw [hveq]
    exact mul_mem (mul_mem hω₁mem h) hω₂mem
  · intro h
    have hueq : u = ω₁⁻¹ * v * ω₂⁻¹ := by
      rw [hveq]
      group
    rw [hueq]
    exact mul_mem (mul_mem (inv_mem hω₁mem) h) (inv_mem hω₂mem)

include k in
/-- Existence form of the reshaping: the reshaped pencil unit exists
and is `stableUnits`-equivalent to the original. -/
theorem exists_reshaped_pencil [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (R P : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (hP : L.IsComplete P)
    (C Q : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (hQ : L.IsComplete Q)
    (E : ι → κ → A) (u : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j,
      L.wordS (R.word i) * E i j * L.wordT (C.word j)) :
    ∃ v : Aˣ, ((v : A) = ∑ i, ∑ j,
      L.wordS (P.word i) * E i j * L.wordT (Q.word j)) ∧
      (u ∈ stableUnits A ↔ v ∈ stableUnits A) := by
  classical
  set F : ι → ι → A := fun i i' ↦ if i = i' then 1 else 0 with hFdef
  set G : κ → κ → A := fun j j' ↦ if j = j' then 1 else 0 with hGdef
  have hFF : ∀ i i' : ι, (∑ j, F i j * F j i') =
      if i = i' then (1 : A) else 0 := by
    intro i i'
    rw [Finset.sum_congr rfl (fun j _ ↦
      show F i j * F j i' = if i = j then F j i' else 0 from by
        show (if i = j then (1 : A) else 0) * F j i' = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ i (fun j ↦ F j i'),
      if_pos (Finset.mem_univ i)]
  have hGG : ∀ j j' : κ, (∑ l, G j l * G l j') =
      if j = j' then (1 : A) else 0 := by
    intro j j'
    rw [Finset.sum_congr rfl (fun l _ ↦
      show G j l * G l j' = if j = l then G l j' else 0 from by
        show (if j = l then (1 : A) else 0) * G l j' = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ j (fun l ↦ G l j'),
      if_pos (Finset.mem_univ j)]
  set ω₁ : Aˣ := L.codePairUnit P hP R hR F F hFF hFF with hω₁
  set ω₂ : Aˣ := L.codePairUnit C hC Q hQ G G hGG hGG with hω₂
  have hcollapseL : ∀ (i : ι) (l : κ), (∑ j, F i j * E j l) = E i l := by
    intro i l
    rw [Finset.sum_congr rfl (fun j _ ↦
      show F i j * E j l = if i = j then E j l else 0 from by
        show (if i = j then (1 : A) else 0) * E j l = _
        split_ifs <;> simp),
      Finset.sum_ite_eq Finset.univ i (fun j ↦ E j l),
      if_pos (Finset.mem_univ i)]
  have hcollapseR : ∀ (i : ι) (l : κ), (∑ j, E i j * G j l) = E i l := by
    intro i l
    rw [Finset.sum_congr rfl (fun j _ ↦
      show E i j * G j l = if j = l then E i j else 0 from by
        show E i j * (if j = l then (1 : A) else 0) = _
        split_ifs <;> simp),
      Finset.sum_ite_eq' Finset.univ l (fun j ↦ E i j),
      if_pos (Finset.mem_univ l)]
  have hval : ((ω₁ * u * ω₂ : Aˣ) : A) = ∑ i, ∑ j,
      L.wordS (P.word i) * E i j * L.wordT (Q.word j) := by
    rw [Units.val_mul, Units.val_mul, hω₁, L.codePairUnit_val, hu,
      L.codePair_mul R P.word C.word F E]
    simp only [hcollapseL]
    rw [hω₂, L.codePairUnit_val,
      L.codePair_mul C P.word Q.word E G]
    simp only [hcollapseR]
  exact ⟨ω₁ * u * ω₂, hval,
    L.reshaped_pencil_mem_iff (k := k) hdiv R P hR hP C Q hC hQ E u
      (ω₁ * u * ω₂) hu hval⟩

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The value window of a pencil over depth-controlled codes**:
entry windows shift by row depth minus column depth. -/
theorem pencilVal_window_mem {a b lo hi : ℤ}
    (P : BinaryPrefixCode ι) (Q : BinaryPrefixCode κ)
    (E : ι → κ → A)
    (hE : ∀ i j, E i j ∈ Submodule.span k (L.degreeMonomials a b))
    (hlo : ∀ i j, lo ≤ ((P.word i).length : ℤ) + a -
      ((Q.word j).length : ℤ))
    (hhi : ∀ i j, ((P.word i).length : ℤ) + b -
      ((Q.word j).length : ℤ) ≤ hi) :
    (∑ i, ∑ j, L.wordS (P.word i) * E i j * L.wordT (Q.word j)) ∈
      Submodule.span k (L.degreeMonomials lo hi) := by
  refine Submodule.sum_mem _ fun i _ ↦
    Submodule.sum_mem _ fun j _ ↦ ?_
  have hS : L.wordS (P.word i) ∈ Submodule.span k
      (L.degreeMonomials ((P.word i).length : ℤ)
        ((P.word i).length : ℤ)) :=
    Submodule.subset_span ⟨P.word i, [], by simp, by simp,
      by rw [wordT_nil, mul_one]⟩
  have hT : L.wordT (Q.word j) ∈ Submodule.span k
      (L.degreeMonomials (-((Q.word j).length : ℤ))
        (-((Q.word j).length : ℤ))) :=
    Submodule.subset_span ⟨[], Q.word j, by simp, by simp,
      by rw [wordS_nil, one_mul]⟩
  have h1 := L.window_mul_mem_span (k := k)
    (L.window_mul_mem_span (k := k) hS (hE i j)) hT
  refine L.span_degreeMonomials_mono ?_ ?_ h1
  · have := hlo i j
    omega
  · have := hhi i j
    omega

end LeavittFamily
end NonsoficGroupsExist
