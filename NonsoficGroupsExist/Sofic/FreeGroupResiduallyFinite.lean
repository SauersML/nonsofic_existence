import NonsoficGroupsExist.Sofic.LEFSofic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Free groups are residually finite, hence sofic

The classical finite-quotient argument, carried out on the ball of radius
`n` around the identity.  Fix a nontrivial element `w` of a free group and
let `L` be its reduced word, of length `n`.  Each generator `a` acts on the
set `{0, …, n}` of *positions* by a partial injection read off from `L`:
if the `i`-th letter of `L` (positions from the left, zero-based) is `a`
with exponent `+1`, the letter moves the point `n - 1 - i` to `n - i`; if
it is `a` with exponent `-1`, it moves `n - i` to `n - 1 - i`.  Because `L`
is reduced, these clauses never conflict: a conflict is precisely an
adjacent cancelling pair.  Each partial injection extends to a genuine
permutation of the ball by matching up the complements of its domain and
range, which have equal cardinality.

The universal property of the free group turns the letter permutations into
a homomorphism to a finite symmetric group, and a telescoping computation
along the word shows the image of `w` moves `0` to `n ≠ 0`.  So every
nontrivial element survives in a finite quotient: free groups are
residually finite, hence LEF, hence sofic.

The construction consumes only the reduced-word interface of
`Mathlib.GroupTheory.FreeGroup.Reduce`: `IsReduced` as a chain condition on
adjacent letters, `isReduced_toWord`, `mk_toWord`, `toWord_eq_nil_iff`, and
`lift_mk`.
-/

namespace NonsoficGroupsExist
namespace FreeGroupBall

open scoped Classical

variable {α : Type*} (L : List (α × Bool))

/-! ### Letters of the word, by position -/

/-- The letter at position `i` is `a` with exponent `+1`. -/
def PlusAt (a : α) (i : ℕ) : Prop :=
  ∃ h : i < L.length, L[i]'h = (a, true)

/-- The letter at position `i` is `a` with exponent `-1`. -/
def MinusAt (a : α) (i : ℕ) : Prop :=
  ∃ h : i < L.length, L[i]'h = (a, false)

/-- A reduced word has no letter followed by its inverse. -/
theorem not_plus_minus (hred : FreeGroup.IsReduced L) {a : α} {i : ℕ}
    (h1 : PlusAt L a i) (h2 : MinusAt L a (i + 1)) : False := by
  obtain ⟨hi1, hget1⟩ := h1
  obtain ⟨hi2, hget2⟩ := h2
  have hc := List.IsChain.getElem hred i hi2
  rw [hget1, hget2] at hc
  simpa using hc rfl

/-- A reduced word has no inverse letter followed by the letter. -/
theorem not_minus_plus (hred : FreeGroup.IsReduced L) {a : α} {i : ℕ}
    (h1 : MinusAt L a i) (h2 : PlusAt L a (i + 1)) : False := by
  obtain ⟨hi1, hget1⟩ := h1
  obtain ⟨hi2, hget2⟩ := h2
  have hc := List.IsChain.getElem hred i hi2
  rw [hget1, hget2] at hc
  simpa using hc rfl

/-! ### The partial injection of a generator, and its extension -/

/-- `x` is moved by the partial injection of `a`: either the letter at
position `n - 1 - x` is `a⁺`, or the letter at position `n - x` is
`a⁻`. -/
def IsSource (a : α) (x : Fin (L.length + 1)) : Prop :=
  (x.val < L.length ∧ PlusAt L a (L.length - 1 - x.val)) ∨
    (0 < x.val ∧ MinusAt L a (L.length - x.val))

/-- `y` is hit by the partial injection of `a`. -/
def IsTarget (a : α) (y : Fin (L.length + 1)) : Prop :=
  (0 < y.val ∧ PlusAt L a (L.length - y.val)) ∨
    (y.val < L.length ∧ MinusAt L a (L.length - 1 - y.val))

/-- The forward map: `+1` letters push a point up, `-1` letters push it
down.  Away from sources it is the identity; it is bijective only after
the complement matching below. -/
noncomputable def fwd (a : α) (x : Fin (L.length + 1)) :
    Fin (L.length + 1) :=
  if h : x.val < L.length ∧ PlusAt L a (L.length - 1 - x.val) then
    ⟨x.val + 1, by omega⟩
  else if h' : 0 < x.val ∧ MinusAt L a (L.length - x.val) then
    ⟨x.val - 1, by omega⟩
  else x

/-- The backward map, inverse to `fwd` between sources and targets. -/
noncomputable def bwd (a : α) (y : Fin (L.length + 1)) :
    Fin (L.length + 1) :=
  if h : 0 < y.val ∧ PlusAt L a (L.length - y.val) then
    ⟨y.val - 1, by omega⟩
  else if h' : y.val < L.length ∧ MinusAt L a (L.length - 1 - y.val) then
    ⟨y.val + 1, by omega⟩
  else y

variable {L}

theorem fwd_mem_target (hred : FreeGroup.IsReduced L) (a : α)
    {x : Fin (L.length + 1)} (hx : IsSource L a x) :
    IsTarget L a (fwd L a x) := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [fwd, dif_pos ⟨h1, h2⟩]
    exact Or.inl ⟨Nat.succ_pos _,
      by rwa [show L.length - (x.val + 1) = L.length - 1 - x.val from by
        omega]⟩
  · have hneg : ¬ (x.val < L.length ∧
        PlusAt L a (L.length - 1 - x.val)) := by
      rintro ⟨hc1, hc2⟩
      exact not_plus_minus L hred hc2
        (by rwa [show (L.length - 1 - x.val) + 1 = L.length - x.val from by
          omega])
    rw [fwd, dif_neg hneg, dif_pos ⟨h1, h2⟩]
    refine Or.inr ⟨by omega, ?_⟩
    rwa [show L.length - 1 - (x.val - 1) = L.length - x.val from by omega]

theorem bwd_mem_source (hred : FreeGroup.IsReduced L) (a : α)
    {y : Fin (L.length + 1)} (hy : IsTarget L a y) :
    IsSource L a (bwd L a y) := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [bwd, dif_pos ⟨h1, h2⟩]
    refine Or.inl ⟨by omega, ?_⟩
    rwa [show L.length - 1 - (y.val - 1) = L.length - y.val from by omega]
  · have hneg : ¬ (0 < y.val ∧ PlusAt L a (L.length - y.val)) := by
      rintro ⟨-, hpl⟩
      exact not_minus_plus L hred h2
        (by rwa [show (L.length - 1 - y.val) + 1 = L.length - y.val from by
          omega])
    rw [bwd, dif_neg hneg, dif_pos ⟨h1, h2⟩]
    exact Or.inr ⟨Nat.succ_pos _,
      by rwa [show L.length - (y.val + 1) = L.length - 1 - y.val from by
        omega]⟩

theorem bwd_fwd (hred : FreeGroup.IsReduced L) (a : α)
    {x : Fin (L.length + 1)} (hx : IsSource L a x) :
    bwd L a (fwd L a x) = x := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [fwd, dif_pos ⟨h1, h2⟩, bwd,
      dif_pos ⟨Nat.succ_pos _,
        by rwa [show L.length - (x.val + 1) = L.length - 1 - x.val from by
          omega]⟩]
    exact Fin.ext (by omega)
  · have hneg : ¬ (x.val < L.length ∧
        PlusAt L a (L.length - 1 - x.val)) := by
      rintro ⟨hc1, hc2⟩
      exact not_plus_minus L hred hc2
        (by rwa [show (L.length - 1 - x.val) + 1 = L.length - x.val from by
          omega])
    rw [fwd, dif_neg hneg, dif_pos ⟨h1, h2⟩, bwd]
    have hneg' : ¬ (0 < (x.val - 1 : ℕ) ∧
        PlusAt L a (L.length - (x.val - 1))) := by
      rintro ⟨-, hpl⟩
      exact not_minus_plus L hred h2
        (by rwa [show L.length - (x.val - 1) =
            (L.length - x.val) + 1 from by omega] at hpl)
    rw [dif_neg hneg',
      dif_pos ⟨by omega,
        by rwa [show L.length - 1 - (x.val - 1) = L.length - x.val from by
          omega]⟩]
    exact Fin.ext (by omega)

theorem fwd_bwd (hred : FreeGroup.IsReduced L) (a : α)
    {y : Fin (L.length + 1)} (hy : IsTarget L a y) :
    fwd L a (bwd L a y) = y := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [bwd, dif_pos ⟨h1, h2⟩, fwd,
      dif_pos ⟨by omega,
        by rwa [show L.length - 1 - (y.val - 1) = L.length - y.val from by
          omega]⟩]
    exact Fin.ext (by omega)
  · have hneg : ¬ (0 < y.val ∧ PlusAt L a (L.length - y.val)) := by
      rintro ⟨-, hpl⟩
      exact not_minus_plus L hred h2
        (by rwa [show (L.length - 1 - y.val) + 1 = L.length - y.val from by
          omega])
    rw [bwd, dif_neg hneg, dif_pos ⟨h1, h2⟩, fwd]
    have hneg' : ¬ ((y.val + 1 : ℕ) < L.length ∧
        PlusAt L a (L.length - 1 - (y.val + 1))) := by
      rintro ⟨hc1, hc2⟩
      exact not_plus_minus L hred hc2
        (by rwa [show (L.length - 1 - (y.val + 1)) + 1 =
            L.length - 1 - y.val from by omega])
    rw [dif_neg hneg',
      dif_pos ⟨Nat.succ_pos _,
        by rwa [show L.length - (y.val + 1) = L.length - 1 - y.val from by
          omega]⟩]
    exact Fin.ext (by omega)

/-- The partial injection of a generator, as an equivalence from its
sources to its targets. -/
noncomputable def sourceTargetEquiv (hred : FreeGroup.IsReduced L)
    (a : α) :
    {x : Fin (L.length + 1) // IsSource L a x} ≃
      {y : Fin (L.length + 1) // IsTarget L a y} where
  toFun x := ⟨fwd L a x.1, fwd_mem_target hred a x.2⟩
  invFun y := ⟨bwd L a y.1, bwd_mem_source hred a y.2⟩
  left_inv x := Subtype.ext (bwd_fwd hred a x.2)
  right_inv y := Subtype.ext (fwd_bwd hred a y.2)

theorem card_compl_eq (hred : FreeGroup.IsReduced L) (a : α) :
    Fintype.card {x : Fin (L.length + 1) // ¬ IsSource L a x} =
      Fintype.card {y : Fin (L.length + 1) // ¬ IsTarget L a y} := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    Fintype.card_congr (sourceTargetEquiv hred a)]

/-- The letter permutation: the partial injection on its sources, glued to
an arbitrary matching of the equally-sized complements. -/
noncomputable def letterPerm (hred : FreeGroup.IsReduced L) (a : α) :
    Equiv.Perm (Fin (L.length + 1)) :=
  (Equiv.sumCompl (IsSource L a)).symm.trans
    (((sourceTargetEquiv hred a).sumCongr
        (Fintype.equivOfCardEq (card_compl_eq hred a))).trans
      (Equiv.sumCompl (IsTarget L a)))

theorem letterPerm_apply_of_isSource (hred : FreeGroup.IsReduced L)
    (a : α) {x : Fin (L.length + 1)} (hx : IsSource L a x) :
    letterPerm hred a x = fwd L a x := by
  rw [letterPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hx]
  rfl

theorem letterPerm_symm_apply_of_isTarget (hred : FreeGroup.IsReduced L)
    (a : α) {y : Fin (L.length + 1)} (hy : IsTarget L a y) :
    (letterPerm hred a).symm y = bwd L a y := by
  rw [letterPerm, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.sumCompl_symm_apply_of_pos hy]
  rfl

/-! ### The word moves the basepoint across the ball -/

variable (L)

/-- The permutation of one letter, exponent included. -/
noncomputable def toLetterPerm (hred : FreeGroup.IsReduced L)
    (x : α × Bool) : Equiv.Perm (Fin (L.length + 1)) :=
  cond x.2 (letterPerm hred x.1) (letterPerm hred x.1)⁻¹

variable {L}

/-- The letter at position `k` moves the point `n - 1 - k` to
`n - k`. -/
theorem toLetterPerm_getElem_apply (hred : FreeGroup.IsReduced L)
    {k : ℕ} (hk : k < L.length) {x y : Fin (L.length + 1)}
    (hx : x.val = L.length - 1 - k) (hy : y.val = L.length - k) :
    toLetterPerm L hred (L[k]'hk) x = y := by
  cases hb : (L[k]'hk).2 with
  | true =>
      simp only [toLetterPerm, hb, cond_true]
      have hplus : PlusAt L (L[k]'hk).1 k := ⟨hk, by rw [← hb]⟩
      have hc : x.val < L.length ∧
          PlusAt L (L[k]'hk).1 (L.length - 1 - x.val) :=
        ⟨by omega,
          by rw [hx,
            show L.length - 1 - (L.length - 1 - k) = k from by omega]
             exact hplus⟩
      rw [letterPerm_apply_of_isSource hred _ (Or.inl hc), fwd,
        dif_pos hc]
      exact Fin.ext (by omega)
  | false =>
      simp only [toLetterPerm, hb, cond_false]
      have hminus : MinusAt L (L[k]'hk).1 k := ⟨hk, by rw [← hb]⟩
      have hc : x.val < L.length ∧
          MinusAt L (L[k]'hk).1 (L.length - 1 - x.val) :=
        ⟨by omega,
          by rw [hx,
            show L.length - 1 - (L.length - 1 - k) = k from by omega]
             exact hminus⟩
      have hneg : ¬ (0 < x.val ∧
          PlusAt L (L[k]'hk).1 (L.length - x.val)) := by
        rintro ⟨-, hpl⟩
        exact not_minus_plus L hred hminus
          (by rwa [show L.length - x.val = k + 1 from by omega] at hpl)
      rw [show (letterPerm hred (L[k]'hk).1)⁻¹ =
          (letterPerm hred (L[k]'hk).1).symm from rfl,
        letterPerm_symm_apply_of_isTarget hred _ (Or.inr hc), bwd,
        dif_neg hneg, dif_pos hc]
      exact Fin.ext (by omega)

/-- Telescoping along the word: the product of the letter permutations of
the last `j` letters moves `0` to `j`. -/
theorem prod_map_drop_apply (hred : FreeGroup.IsReduced L) :
    ∀ j : ℕ, ∀ hj : j ≤ L.length,
      ((L.drop (L.length - j)).map (toLetterPerm L hred)).prod
          ⟨0, Nat.succ_pos _⟩ = ⟨j, by omega⟩ := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_length]
      rfl
  | succ j ih =>
      intro hj
      have hk : L.length - (j + 1) < L.length := by omega
      rw [List.drop_eq_getElem_cons hk, List.map_cons, List.prod_cons,
        Equiv.Perm.mul_apply,
        show L.length - (j + 1) + 1 = L.length - j from by omega,
        ih (by omega)]
      exact toLetterPerm_getElem_apply hred hk (by omega) (by omega)

/-! ### The finite quotient detecting a nontrivial element -/

/-- The homomorphism to the symmetric group of the ball. -/
noncomputable def wordHom (hred : FreeGroup.IsReduced L) :
    FreeGroup α →* Equiv.Perm (Fin (L.length + 1)) :=
  FreeGroup.lift fun a => letterPerm hred a

theorem wordHom_apply_zero (w : FreeGroup α) :
    wordHom (L := w.toWord) FreeGroup.isReduced_toWord w
        ⟨0, Nat.succ_pos _⟩ =
      ⟨w.toWord.length, Nat.lt_succ_self _⟩ := by
  have hkey : wordHom (L := w.toWord) FreeGroup.isReduced_toWord
      (FreeGroup.mk w.toWord) ⟨0, Nat.succ_pos _⟩ =
      ⟨w.toWord.length, Nat.lt_succ_self _⟩ := by
    rw [wordHom, FreeGroup.lift_mk]
    have h := prod_map_drop_apply (L := w.toWord)
      FreeGroup.isReduced_toWord w.toWord.length le_rfl
    rwa [Nat.sub_self, List.drop_zero] at h
  rwa [FreeGroup.mk_toWord] at hkey

theorem wordHom_ne_one (w : FreeGroup α) (hw : w ≠ 1) :
    wordHom (L := w.toWord) FreeGroup.isReduced_toWord w ≠ 1 := by
  intro hcon
  have h0 := wordHom_apply_zero w
  rw [hcon, Equiv.Perm.one_apply] at h0
  have hlen : (0 : ℕ) = w.toWord.length := congrArg Fin.val h0
  exact hw (FreeGroup.toWord_eq_nil_iff.mp
    (List.length_eq_zero_iff.mp hlen.symm))

end FreeGroupBall

/-- **Free groups are residually finite**: every nontrivial element is
detected by a homomorphism to a finite symmetric group, acting on the ball
of the element's own word length. -/
instance freeGroup_residuallyFinite (α : Type*) :
    Group.ResiduallyFinite (FreeGroup α) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom.{0}
  intro w hw
  exact ⟨Equiv.Perm (Fin (w.toWord.length + 1)), inferInstance,
    inferInstance,
    FreeGroupBall.wordHom (L := w.toWord) FreeGroup.isReduced_toWord,
    FreeGroupBall.wordHom_ne_one w hw⟩

/-- Free groups are sofic, through residual finiteness and local
embeddability. -/
theorem isSofic_freeGroup (α : Type*) : IsSofic (FreeGroup α) :=
  isSofic_of_isLEF isLEF_of_residuallyFinite

end NonsoficGroupsExist
