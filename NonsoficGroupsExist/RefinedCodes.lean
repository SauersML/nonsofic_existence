import NonsoficGroupsExist.CodeChangeGlue

/-!
# Uniform refinements of prefix codes

Extending every word of a complete prefix family by all words of a
fixed level yields again a complete prefix family, indexed by the
product; and any element strips over a pair of complete codes into
the double sum of its corner entries.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Extensions of incomparable words are incomparable. -/
theorem not_prefix_append_of_incomparable {a b x y : List (Fin 2)}
    (hab : ¬a <+: b) (hba : ¬b <+: a) :
    ¬(a ++ x) <+: (b ++ y) := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hlen : a.length ≤ b.length
  · exact hab (List.prefix_of_prefix_length_le ha
      (List.prefix_append b y) hlen)
  · exact hba (List.prefix_of_prefix_length_le
      (List.prefix_append b y) ha (by omega))

/-- Distinct same-length extensions of one word are incomparable. -/
theorem not_prefix_append_same {a x y : List (Fin 2)}
    (hlen : x.length = y.length) (hne : x ≠ y) :
    ¬(a ++ x) <+: (a ++ y) := by
  intro h
  have hlen2 : (a ++ x).length = (a ++ y).length := by
    simp [hlen]
  have heq := h.eq_of_length hlen2
  exact hne (List.append_inj_right heq rfl)

/-- A cylinder splits over all extensions of a fixed level. -/
theorem cylinder_level_split (M : ℕ) :
    ∀ w : List (Fin 2), L.cylinder w =
      ∑ α : Fin M → Fin 2, L.cylinder (w ++ List.ofFn α) := by
  induction M with
  | zero =>
      intro w
      rw [Fintype.sum_unique
        (fun α : Fin 0 → Fin 2 ↦ L.cylinder (w ++ List.ofFn α)),
        List.ofFn_zero, List.append_nil]
  | succ M ih =>
      intro w
      calc L.cylinder w
          = L.cylinder (w ++ [0]) + L.cylinder (w ++ [1]) :=
            L.cylinder_split w
        _ = ∑ z : Fin 2, L.cylinder (w ++ [z]) := by
            rw [Fin.sum_univ_two]
        _ = ∑ z : Fin 2, ∑ α : Fin M → Fin 2,
            L.cylinder ((w ++ [z]) ++ List.ofFn α) :=
            Finset.sum_congr rfl fun z _ ↦ ih (w ++ [z])
        _ = ∑ z : Fin 2, ∑ α : Fin M → Fin 2,
            L.cylinder (w ++ List.ofFn (Fin.cons z α)) := by
            refine Finset.sum_congr rfl fun z _ ↦
              Finset.sum_congr rfl fun α _ ↦ ?_
            rw [show w ++ List.ofFn (Fin.cons z α) =
              (w ++ [z]) ++ List.ofFn α from by
                rw [List.ofFn_succ]
                -- `List.append_cons` rewrites `l ++ a :: m` to `l ++ [a] ++ m`,
                -- whose own `[a] ++ m` matches the pattern again; reassociate
                -- instead of splitting off the head.
                simp only [Fin.cons_zero, Fin.cons_succ,
                  List.append_assoc, List.singleton_append]]
        _ = ∑ p : Fin 2 × (Fin M → Fin 2),
            L.cylinder (w ++ List.ofFn (Fin.cons p.1 p.2)) := by
            -- as a `rw` the summand is determined first-order by matching the
            -- product sum; passing `_` instead makes it a higher-order unfold
            -- through the `Fin M → Fin 2` `Fintype` instance, which times out.
            rw [Fintype.sum_prod_type]
        _ = ∑ α : Fin (M + 1) → Fin 2,
            L.cylinder (w ++ List.ofFn α) :=
            Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Fin 2) _ _
              fun p ↦ rfl

/-- The uniformly refined family is prefix-free. -/
theorem refined_free {κ : Type*} (Ccode : BinaryPrefixCode κ)
    (M : ℕ) :
    ∀ ⦃p q : κ × (Fin M → Fin 2)⦄, p ≠ q →
      ¬(Ccode.word p.1 ++ List.ofFn p.2) <+:
        (Ccode.word q.1 ++ List.ofFn q.2) := by
  rintro ⟨j, α⟩ ⟨j', α'⟩ hne h
  by_cases hjj : j = j'
  · subst hjj
    have hαα : α ≠ α' := fun hh ↦ hne (by rw [hh])
    exact not_prefix_append_same (by simp)
      (fun hh ↦ hαα (List.ofFn_inj.mp hh)) h
  · exact not_prefix_append_of_incomparable
      (Ccode.prefix_free hjj) (Ccode.prefix_free (Ne.symm hjj)) h

/-- The uniformly refined family is complete. -/
theorem refined_sum {κ : Type*} [Fintype κ]
    (Ccode : BinaryPrefixCode κ) (hC : L.IsComplete Ccode) (M : ℕ) :
    ∑ p : κ × (Fin M → Fin 2),
      L.cylinder (Ccode.word p.1 ++ List.ofFn p.2) = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl
    (fun j _ ↦ (L.cylinder_level_split M (Ccode.word j)).symm)]
  exact hC

/-- Any element strips over a pair of complete codes into its corner
entries. -/
theorem codePair_partition {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ccode : BinaryPrefixCode κ) (hC : L.IsComplete Ccode)
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (x : A) :
    x = ∑ j, ∑ i, L.wordS (Ccode.word j) *
      (L.wordT (Ccode.word j) * x * L.wordS (R.word i)) *
      L.wordT (R.word i) := by
  calc x = 1 * x * 1 := by rw [one_mul, mul_one]
    _ = (∑ j, L.cylinder (Ccode.word j)) * x *
        (∑ i, L.cylinder (R.word i)) := by rw [hC, hR]
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [cylinder]
        noncomm_ring

end LeavittFamily
end NonsoficGroupsExist
