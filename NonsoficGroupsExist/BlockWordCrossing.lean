import NonsoficGroupsExist.GeneratorWords
import NonsoficGroupsExist.MatchedComponents
import NonsoficGroupsExist.SoficErrors

/-!
# Propagating block invariance along words

Almost invariance of the component partition is supplied on a finite symmetric
generating set.  This file proves the manuscript's repeated use of
Lemma `lem:word`: crossings of an evaluated word are bounded by the sum of its
letter crossings, and replacing the evaluated word by the assigned
permutation costs one negligible disagreement set.
-/

namespace NonsoficGroupsExist

variable {Y : FiniteModel}

/-- The preimage of a finset under a permutation. -/
def permutationPreimage (p : Equiv.Perm Y) (A : Finset Y) : Finset Y :=
  Finset.univ.filter fun x ↦ p x ∈ A

theorem permutationPreimage_card (p : Equiv.Perm Y) (A : Finset Y) :
    (permutationPreimage p A).card = A.card := by
  classical
  have heq : permutationPreimage p A = A.image p.symm := by
    ext x
    simp only [permutationPreimage, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hx
      exact ⟨p x, hx, p.symm_apply_apply x⟩
    · rintro ⟨y, hy, hxy⟩
      have := congrArg p hxy
      have hpx : p x = y := by simpa using this.symm
      rw [hpx]
      exact hy
  rw [heq, Finset.card_image_of_injective _ p.symm.injective]

theorem wordCrossing_mul_subset (P : BlockStructure Y) (p q : Equiv.Perm Y) :
    wordCrossing P (p * q) ⊆
      wordCrossing P q ∪ permutationPreimage q (wordCrossing P p) := by
  classical
  intro x hx
  simp only [wordCrossing, permutationPreimage, Equiv.Perm.mul_apply,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hq : P.block (q x) ≠ P.block x
  · exact Or.inl hq
  · right
    intro hp
    exact hx (hp.trans (not_ne_iff.mp hq))

theorem wordCrossing_mul_card_le (P : BlockStructure Y) (p q : Equiv.Perm Y) :
    (wordCrossing P (p * q)).card ≤
      (wordCrossing P q).card + (wordCrossing P p).card := by
  have hs := Finset.card_le_card (wordCrossing_mul_subset P p q)
  have hu := Finset.card_union_le (wordCrossing P q)
    (permutationPreimage q (wordCrossing P p))
  rw [permutationPreimage_card] at hu
  omega

namespace SoficApproximation

variable {G : Type} [Group G] (S : SoficApproximation G)
variable (P : ∀ n, BlockStructure (S.model n))

/-- Disagreement between the assigned value of a word and its letterwise
evaluation. -/
noncomputable def wordDisagreement (w : List G) (n : ℕ) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦
    S.map n w.prod x ≠ SoficApproximation.evaluateWord (S.map n) w x

theorem wordDisagreement_negligible (w : List G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.wordDisagreement w n).card : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := S.word_close w ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  change |((S.wordDisagreement w n).card : ℝ) / Fintype.card (S.model n)| < ε
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  simpa only [hammingDistance, wordDisagreement] using hN n hn

private theorem evaluateWord_crossing_card_le (w : List G) (n : ℕ) :
    (wordCrossing (P n) (SoficApproximation.evaluateWord (S.map n) w)).card ≤
      (w.map fun g ↦ (wordCrossing (P n) (S.map n g)).card).sum := by
  induction w with
  | nil => simp [SoficApproximation.evaluateWord, wordCrossing]
  | cons g w ih =>
      have hm := wordCrossing_mul_card_le (P n) (S.map n g)
        (SoficApproximation.evaluateWord (S.map n) w)
      simp only [SoficApproximation.evaluateWord, List.map_cons, List.sum_cons]
      omega

private theorem evaluateWord_crossing_negligible (w : List G)
    (hletter : ∀ g ∈ w, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((wordCrossing (P n)
        (SoficApproximation.evaluateWord (S.map n) w)).card : ℝ) := by
  induction w with
  | nil =>
      simpa [SoficApproximation.evaluateWord, wordCrossing] using
        (Negligible.zero : Negligible
          (fun n ↦ (Fintype.card (S.model n) : ℝ)) (fun _ ↦ 0))
  | cons g w ih =>
      have hg := hletter g (by simp)
      have hw := ih fun x hx ↦ hletter x (by simp [hx])
      have hsum := Negligible.add hw hg
      refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
        (fun n ↦ ?_) hsum
      have hcard := wordCrossing_mul_card_le (P n) (S.map n g)
        (SoficApproximation.evaluateWord (S.map n) w)
      have hcast :
          ((wordCrossing (P n)
            (SoficApproximation.evaluateWord (S.map n) (g :: w))).card : ℝ) ≤
          ((wordCrossing (P n)
            (SoficApproximation.evaluateWord (S.map n) w)).card : ℝ) +
          (wordCrossing (P n) (S.map n g)).card := by
        exact_mod_cast hcard
      apply div_le_div_of_nonneg_right hcast
      positivity

private theorem assigned_crossing_subset (w : List G) (n : ℕ) :
    wordCrossing (P n) (S.map n w.prod) ⊆
      S.wordDisagreement w n ∪
        wordCrossing (P n) (SoficApproximation.evaluateWord (S.map n) w) := by
  classical
  intro x hx
  simp only [wordCrossing, wordDisagreement, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union] at hx ⊢
  by_cases hd : S.map n w.prod x ≠
      SoficApproximation.evaluateWord (S.map n) w x
  · exact Or.inl hd
  · right
    rw [← not_ne_iff.mp hd]
    exact hx

theorem wordCrossing_negligible_of_letters (w : List G)
    (hletter : ∀ g ∈ w, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n w.prod)).card : ℝ) := by
  have hsum := Negligible.add (S.wordDisagreement_negligible w)
    (S.evaluateWord_crossing_negligible P w hletter)
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hs := Finset.card_le_card (S.assigned_crossing_subset P w n)
  have hu := Finset.card_union_le (S.wordDisagreement w n)
    (wordCrossing (P n) (SoficApproximation.evaluateWord (S.map n) w))
  have hcast : ((wordCrossing (P n) (S.map n w.prod)).card : ℝ) ≤
      ((S.wordDisagreement w n).card : ℝ) +
        (wordCrossing (P n)
          (SoficApproximation.evaluateWord (S.map n) w)).card := by
    exact_mod_cast hs.trans hu
  apply div_le_div_of_nonneg_right hcast
  positivity

/-- Generator almost-invariance propagates to every fixed group element. -/
theorem all_wordCrossing_negligible (T : Finset G)
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤)
    (hgenerator : ∀ g ∈ T, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ))
    (g : G) : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ) := by
  obtain ⟨w, hw, hprod⟩ := exists_generator_word T hsymm hgen g
  rw [← hprod]
  exact S.wordCrossing_negligible_of_letters P w fun x hx ↦ hgenerator x (hw x hx)

end SoficApproximation
end NonsoficGroupsExist
