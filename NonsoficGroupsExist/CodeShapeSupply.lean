import NonsoficGroupsExist.CompleteCodeSupply
import NonsoficGroupsExist.LeavittDegreeZero

/-!
# Deep complete codes of every admissible size

The session-54 exits reshape a pencil's codes into depth-controlled
ones.  The single construction needed: a complete prefix family of
any size `m ≥ 2^M` with every word of depth at least `M` — the full
level-`M` code followed by `m − 2^M` splits, each of which only
deepens words.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- **Deep complete prefix families**: any size `m ≥ 2^M`, all words
of depth at least `M`. -/
theorem exists_complete_deep_family (M : ℕ) : ∀ m : ℕ, 2 ^ M ≤ m →
    ∃ w : Fin m → List (Fin 2),
      (∀ ⦃i j : Fin m⦄, i ≠ j → ¬w i <+: w j) ∧
      (∑ i, L.cylinder (w i) = 1) ∧
      ∀ i, M ≤ (w i).length := by
  have hM1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
      intro hn
      by_cases h2 : 2 ^ M ≤ n
      · obtain ⟨w, hfree, hsum, hdeep⟩ := ih h2
        set j₀ : Fin n := ⟨0, by omega⟩ with hj₀
        have hfree' := split_family_free w hfree j₀
        have hsum' := L.split_family_sum w hsum j₀
        have hcard : Fintype.card (Fin (n + 1)) =
            Fintype.card (Fin 2 ⊕ {i : Fin n // i ≠ j₀}) := by
          rw [Fintype.card_sum, Fintype.card_subtype_compl,
            Fintype.card_subtype_eq]
          simp only [Fintype.card_fin]
          omega
        set e := Fintype.equivOfCardEq hcard with he
        obtain ⟨hf, hs⟩ := L.family_transport e
          (Sum.elim (fun z ↦ w j₀ ++ [z]) (fun i ↦ w i.1))
          hfree' hsum'
        refine ⟨_, hf, hs, ?_⟩
        intro p
        show M ≤ ((Sum.elim (fun z ↦ w j₀ ++ [z])
          (fun i ↦ w i.1)) (e p)).length
        rcases e p with z | i
        · rw [Sum.elim_inl, List.length_append]
          have := hdeep j₀
          omega
        · rw [Sum.elim_inr]
          exact hdeep i.1
      · -- `n + 1 = 2^M`: the full level-`M` code
        have hcard : Fintype.card (Fin (n + 1)) =
            Fintype.card (Fin M → Fin 2) := by
          simp only [Fintype.card_fin, Fintype.card_fun]
          omega
        set e := Fintype.equivOfCardEq hcard with he
        obtain ⟨hf, hs⟩ := L.family_transport e
          (fun f : Fin M → Fin 2 ↦ List.ofFn f)
          (fullBinaryCode M).prefix_free
          (L.fullBinaryCode_complete M)
        refine ⟨_, hf, hs, ?_⟩
        intro p
        show M ≤ (List.ofFn (e p)).length
        simp

/-- Deep complete codes, packaged. -/
theorem exists_deep_code (M m : ℕ) (h : 2 ^ M ≤ m) :
    ∃ D : BinaryPrefixCode (Fin m),
      L.IsComplete D ∧ ∀ i, M ≤ (D.word i).length := by
  obtain ⟨w, hfree, hsum, hdeep⟩ := L.exists_complete_deep_family M m h
  exact ⟨⟨w, hfree⟩, hsum, hdeep⟩

end LeavittFamily
end NonsoficGroupsExist
