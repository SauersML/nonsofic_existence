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

/-- **Shallow complete prefix families**: any size `1 ≤ κ ≤ 2^r`,
all words of depth at most `r` — by recursive halving. -/
theorem exists_shallow_family : ∀ r κ : ℕ, 1 ≤ κ → κ ≤ 2 ^ r →
    ∃ w : Fin κ → List (Fin 2),
      (∀ ⦃i j : Fin κ⦄, i ≠ j → ¬w i <+: w j) ∧
      (∑ i, L.cylinder (w i) = 1) ∧
      ∀ i, (w i).length ≤ r := by
  intro r
  induction r with
  | zero =>
      intro κ h1 h2
      rw [pow_zero] at h2
      have hκ : κ = 1 := by omega
      subst hκ
      refine ⟨fun _ ↦ [], ?_, ?_, ?_⟩
      · intro i j hij
        exact absurd (Fin.ext (by omega)) hij
      · rw [Fin.sum_univ_one]
        show L.wordS [] * L.wordT [] = 1
        rw [wordS_nil, wordT_nil, one_mul]
      · intro i
        simp
  | succ r ih =>
      intro κ h1 h2
      by_cases hκ1 : κ = 1
      · subst hκ1
        refine ⟨fun _ ↦ [], ?_, ?_, ?_⟩
        · intro i j hij
          exact absurd (Fin.ext (by omega)) hij
        · rw [Fin.sum_univ_one]
          show L.wordS [] * L.wordT [] = 1
          rw [wordS_nil, wordT_nil, one_mul]
        · intro i
          simp
      · have h2' : κ ≤ 2 ^ r * 2 := by
          rw [pow_succ] at h2
          omega
        obtain ⟨w₀, hf₀, hs₀, hd₀⟩ := ih (κ - κ / 2)
          (by omega) (by omega)
        obtain ⟨w₁, hf₁, hs₁, hd₁⟩ := ih (κ / 2)
          (by omega) (by omega)
        have hWfree : ∀ ⦃p q : Fin (κ - κ / 2) ⊕ Fin (κ / 2)⦄,
            p ≠ q →
            ¬(Sum.elim (fun i ↦ (0 : Fin 2) :: w₀ i)
              (fun i ↦ (1 : Fin 2) :: w₁ i)) p <+:
              (Sum.elim (fun i ↦ (0 : Fin 2) :: w₀ i)
                (fun i ↦ (1 : Fin 2) :: w₁ i)) q := by
          rintro (i₁ | i₁) (i₂ | i₂) hne h
          · have hne' : i₁ ≠ i₂ := fun hh ↦ hne (by rw [hh])
            exact hf₀ hne' (List.cons_prefix_cons.mp h).2
          · exact absurd (List.cons_prefix_cons.mp h).1 (by decide)
          · exact absurd (List.cons_prefix_cons.mp h).1 (by decide)
          · have hne' : i₁ ≠ i₂ := fun hh ↦ hne (by rw [hh])
            exact hf₁ hne' (List.cons_prefix_cons.mp h).2
        have hWsum : ∑ p : Fin (κ - κ / 2) ⊕ Fin (κ / 2),
            L.cylinder ((Sum.elim (fun i ↦ (0 : Fin 2) :: w₀ i)
              (fun i ↦ (1 : Fin 2) :: w₁ i)) p) = 1 := by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          have h₀ : ∑ i, L.cylinder ((0 : Fin 2) :: w₀ i) =
              L.s 0 * L.t 0 := by
            rw [Finset.sum_congr rfl (fun i _ ↦ by
              rw [L.cylinder_cons (0 : Fin 2) (w₀ i), mul_assoc])]
            rw [← Finset.mul_sum, ← Finset.sum_mul, hs₀, one_mul]
          have h₁ : ∑ i, L.cylinder ((1 : Fin 2) :: w₁ i) =
              L.s 1 * L.t 1 := by
            rw [Finset.sum_congr rfl (fun i _ ↦ by
              rw [L.cylinder_cons (1 : Fin 2) (w₁ i), mul_assoc])]
            rw [← Finset.mul_sum, ← Finset.sum_mul, hs₁, one_mul]
          rw [h₀, h₁]
          exact L.sum_s_mul_t
        have hcard : Fintype.card (Fin κ) =
            Fintype.card (Fin (κ - κ / 2) ⊕ Fin (κ / 2)) := by
          rw [Fintype.card_sum]
          simp only [Fintype.card_fin]
          omega
        set e := Fintype.equivOfCardEq hcard with he
        obtain ⟨hf, hs⟩ := L.family_transport e
          (Sum.elim (fun i ↦ (0 : Fin 2) :: w₀ i)
            (fun i ↦ (1 : Fin 2) :: w₁ i)) hWfree hWsum
        refine ⟨_, hf, hs, ?_⟩
        intro p
        show ((Sum.elim (fun i ↦ (0 : Fin 2) :: w₀ i)
          (fun i ↦ (1 : Fin 2) :: w₁ i)) (e p)).length ≤ r + 1
        rcases e p with i | i
        · rw [Sum.elim_inl, List.length_cons]
          have := hd₀ i
          omega
        · rw [Sum.elim_inr, List.length_cons]
          have := hd₁ i
          omega

/-- Shallow complete codes, packaged. -/
theorem exists_shallow_code (r κ : ℕ) (h1 : 1 ≤ κ) (h2 : κ ≤ 2 ^ r) :
    ∃ Q : BinaryPrefixCode (Fin κ),
      L.IsComplete Q ∧ ∀ j, (Q.word j).length ≤ r := by
  obtain ⟨w, hfree, hsum, hd⟩ := L.exists_shallow_family r κ h1 h2
  exact ⟨⟨w, hfree⟩, hsum, hd⟩

end LeavittFamily
end NonsoficGroupsExist
