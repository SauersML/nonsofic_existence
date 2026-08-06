import NonsoficGroupsExist.IncomparableUnipotents
import NonsoficGroupsExist.LeavittBalancedUnits
import NonsoficGroupsExist.LeavittGradingSpans
import NonsoficGroupsExist.DegreeShapeBridge

/-!
# Infrastructure for code-change units

Complete prefix codes as lists of words, and the ingredients of the
generation theorem for code-change units:

* words are nonzero, and a complete prefix code of size at least two
  contains a sibling pair at maximal depth;
* the merge identity `s_{v0} t_{w0} + s_{v1} t_{w1} = s_v t_w`;
* the honest (unsigned) transposition of two incomparable cylinders
  lies in the diagonal class group — the signed swap times a
  balanced sign flip.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- `s`-words are nonzero (in a nontrivial ring). -/
theorem wordS_ne_zero [Nontrivial A] (a : List (Fin 2)) :
    L.wordS a ≠ 0 := by
  intro h
  have h1 : L.wordT a * L.wordS a = 1 := L.wordT_mul_wordS_self a
  rw [h, mul_zero] at h1
  -- `h1 : (0 : A) = 1` already; `.symm` would hand `zero_ne_one` the
  -- wrong orientation.
  exact zero_ne_one h1

/-- A list of words is a complete prefix code: pairwise incomparable
and with cylinders summing to one. -/
structure IsCompleteCode (c : List (List (Fin 2))) : Prop where
  pairwise_incomp : c.Pairwise (fun a b ↦ ¬a <+: b ∧ ¬b <+: a)
  complete : (c.map (fun w ↦ L.cylinder w)).sum = 1

/-- Every nonempty list has a member of maximal image value. -/
theorem exists_max_length_mem {c : List (List (Fin 2))}
    (hne : c ≠ []) :
    ∃ m ∈ c, ∀ x ∈ c, x.length ≤ m.length := by
  induction c with
  | nil => exact absurd rfl hne
  | cons a t ih =>
      rcases eq_or_ne t [] with rfl | hte
      · exact ⟨a, List.mem_cons_self, by
          intro x hx
          rw [List.mem_singleton] at hx
          rw [hx]⟩
      · obtain ⟨m, hm, hmax⟩ := ih hte
        rcases le_or_gt a.length m.length with h | h
        · refine ⟨m, List.mem_cons_of_mem a hm, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact h
          · exact hmax x hx'
        · refine ⟨a, List.mem_cons_self, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact le_refl _
          · exact le_trans (hmax x hx') (le_of_lt h)

/-- If a mapped list sum times an element is nonzero, some term is
nonzero. -/
theorem exists_term_mul_ne_zero {c : List (List (Fin 2))}
    {f : List (Fin 2) → A} {x : A}
    (h : (c.map f).sum * x ≠ 0) :
    ∃ v ∈ c, f v * x ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  -- Induct inside a standalone `have`.  Running `induction c` on the main
  -- goal auto-generalises `h` and `hall` (both mention `c`), so `ih` picks
  -- up extra arguments and `fun v hv ↦ …` ends up binding `v` to a proof.
  have key : ∀ l : List (List (Fin 2)),
      (∀ v ∈ l, f v * x = 0) → (l.map f).sum * x = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
        intro hl
        rw [List.map_cons, List.sum_cons, add_mul,
          hl a List.mem_cons_self, zero_add]
        exact ih fun v hv ↦ hl v (List.mem_cons_of_mem a hv)
  exact key c hall

/-- The merge identity: sibling terms combine. -/
theorem merge_identity_one (v w : List (Fin 2)) :
    L.wordS (v ++ [0]) * L.wordT (w ++ [0]) +
      L.wordS (v ++ [1]) * L.wordT (w ++ [1]) =
    L.wordS v * L.wordT w := by
  rw [L.wordS_append, L.wordS_append, L.wordT_append, L.wordT_append]
  simp only [wordS_cons, wordS_nil, wordT_cons, wordT_nil]
  rw [show L.wordS v * (L.s 0 * 1) * (1 * L.t 0 * L.wordT w) +
      L.wordS v * (L.s 1 * 1) * (1 * L.t 1 * L.wordT w) =
    L.wordS v * (L.s 0 * L.t 0 + L.s 1 * L.t 1) * L.wordT w from by
      noncomm_ring, L.sum_s_mul_t]
  noncomm_ring

/-- Distinct members of a complete code are incomparable. -/
theorem IsCompleteCode.incomp {c : List (List (Fin 2))}
    (hc : L.IsCompleteCode c) {a b : List (Fin 2)} (ha : a ∈ c)
    (hb : b ∈ c) (hab : a ≠ b) : ¬a <+: b ∧ ¬b <+: a := by
  -- `List.Pairwise.forall` now takes symmetry as a `Std.Symm` *instance*
  -- rather than an explicit argument (`Symmetric` itself is deprecated).
  haveI : Std.Symm (fun a b : List (Fin 2) ↦ ¬a <+: b ∧ ¬b <+: a) :=
    ⟨fun _ _ h ↦ ⟨h.2, h.1⟩⟩
  exact hc.pairwise_incomp.forall ha hb hab

/-- **Sibling pair at maximal depth**: a complete prefix code with at
least two elements contains both children of some word. -/
theorem exists_sibling_pair [Nontrivial A] {c : List (List (Fin 2))}
    (hc : L.IsCompleteCode c) (hlen : 2 ≤ c.length) :
    ∃ w : List (Fin 2), (w ++ [0]) ∈ c ∧ (w ++ [1]) ∈ c := by
  classical
  have hne : c ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨m, hm, hmax⟩ := exists_max_length_mem hne
  -- the maximal element is not the empty word
  have hmne : m ≠ [] := by
    intro hmeps
    obtain ⟨x, hx, hxm⟩ : ∃ x ∈ c, x ≠ m := by
      by_contra hall
      push Not at hall
      have : c.length ≤ 1 := by
        rcases c with _ | ⟨a, _ | ⟨b, t⟩⟩
        · simp
        · simp
        · exfalso
          have ha := hall a List.mem_cons_self
          have hb := hall b
            (List.mem_cons_of_mem a List.mem_cons_self)
          have hpair := hc.pairwise_incomp
          rw [List.pairwise_cons] at hpair
          have h1 := hpair.1 b List.mem_cons_self
          rw [ha, hb] at h1
          exact h1.1 (List.prefix_refl m)
      omega
    have h1 := hc.incomp (L := L) hm hx (Ne.symm hxm)
    rw [hmeps] at h1
    exact h1.1 (List.nil_prefix)
  -- write it as `w ++ [a]`
  obtain ⟨w, a, rfl⟩ : ∃ (w : List (Fin 2)) (a : Fin 2),
      m = w ++ [a] := by
    refine ⟨m.dropLast, m.getLast hmne, ?_⟩
    -- `rw` cannot build a motive here: the proof `hmne` mentions `m`, so
    -- abstracting `m` makes `m.getLast hmne` ill-typed.  Use the lemma
    -- directly instead of rewriting with it.
    exact (List.dropLast_append_getLast hmne).symm
  -- the sibling word
  set b : Fin 2 := if a = 0 then 1 else 0 with hb
  have hab : a ≠ b := by
    rw [hb]
    fin_cases a <;> decide
  -- completeness forces the sibling cylinder to be covered
  have hcov : L.wordS (w ++ [b]) ≠ 0 := L.wordS_ne_zero _
  have hsum : (c.map (fun v ↦ L.cylinder v)).sum *
      L.wordS (w ++ [b]) = L.wordS (w ++ [b]) := by
    rw [hc.complete, one_mul]
  have hterm : ∃ v ∈ c, L.cylinder v * L.wordS (w ++ [b]) ≠ 0 := by
    refine exists_term_mul_ne_zero ?_
    rw [hsum]
    exact hcov
  obtain ⟨v, hv, hvne⟩ := hterm
  -- the witness is comparable with the sibling word
  have hcomp : v <+: (w ++ [b]) ∨ (w ++ [b]) <+: v := by
    by_contra hnc
    push Not at hnc
    apply hvne
    rw [cylinder, mul_assoc,
      show L.wordT v * L.wordS (w ++ [b]) = 0 from
        L.wordT_mul_wordS_of_incomparable _ _ hnc.1 hnc.2, mul_zero]
  -- the witness must be the sibling itself
  have hveq : v = w ++ [b] := by
    rcases hcomp with hpre | hpre
    · rcases eq_or_ne v (w ++ [b]) with heq | hne'
      · exact heq
      · exfalso
        have hlenv : v.length ≤ w.length := by
          have h1 := hpre.length_le
          have h2 : v.length ≠ (w ++ [b]).length := by
            intro h
            exact hne' (List.IsPrefix.eq_of_length hpre h)
          simp only [List.length_append, List.length_singleton]
            at h1 h2 ⊢
          omega
        have hvw : v <+: w :=
          List.prefix_of_prefix_length_le hpre
            (List.prefix_append w [b]) hlenv
        have hvm : v <+: (w ++ [a]) :=
          hvw.trans (List.prefix_append w [a])
        have hvnem : v ≠ w ++ [a] := by
          intro h
          rw [h] at hlenv
          simp at hlenv
        exact (hc.incomp (L := L) hv hm hvnem).1 hvm
    · refine (List.IsPrefix.eq_of_length hpre ?_).symm
      have h1 := hpre.length_le
      have h2 := hmax v hv
      simp only [List.length_append, List.length_singleton] at h1 h2 ⊢
      omega
  -- assemble by cases on the last letter
  have hvv : (w ++ [b]) ∈ c := hveq ▸ hv
  fin_cases a
  · refine ⟨w, hm, ?_⟩
    have hb1 : b = 1 := by rw [hb]; rfl
    rwa [hb1] at hvv
  · refine ⟨w, ?_, hm⟩
    have hb0 : b = 0 := by rw [hb]; rfl
    rwa [hb0] at hvv

/-- The balanced sign flip `1 - 2·p_b`, a self-inverse unit. -/
def signFlip (b : List (Fin 2)) : Aˣ where
  val := 1 - (L.cylinder b + L.cylinder b)
  inv := 1 - (L.cylinder b + L.cylinder b)
  val_inv := by
    have hp := L.cylinder_isIdempotent b
    rw [show (1 - (L.cylinder b + L.cylinder b)) *
        (1 - (L.cylinder b + L.cylinder b)) =
      1 - (L.cylinder b + L.cylinder b) -
        (L.cylinder b + L.cylinder b) +
        (L.cylinder b * L.cylinder b + L.cylinder b * L.cylinder b +
          (L.cylinder b * L.cylinder b +
            L.cylinder b * L.cylinder b)) from by noncomm_ring, hp]
    abel
  inv_val := by
    have hp := L.cylinder_isIdempotent b
    rw [show (1 - (L.cylinder b + L.cylinder b)) *
        (1 - (L.cylinder b + L.cylinder b)) =
      1 - (L.cylinder b + L.cylinder b) -
        (L.cylinder b + L.cylinder b) +
        (L.cylinder b * L.cylinder b + L.cylinder b * L.cylinder b +
          (L.cylinder b * L.cylinder b +
            L.cylinder b * L.cylinder b)) from by noncomm_ring, hp]
    abel

section Scalars

variable {k : Type*} [Field k] [Algebra k A]

/-- The sign flip lies in the diagonal class group. -/
theorem signFlip_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (b : List (Fin 2)) :
    L.signFlip b ∈ stableUnits A := by
  have hval : ((L.signFlip b : Aˣ) : A) ∈
      Submodule.span k (L.levelMonomials b.length) := by
    show (1 : A) - (L.cylinder b + L.cylinder b) ∈ _
    refine Submodule.sub_mem _
      (L.one_mem_span_levelMonomials b.length) ?_
    refine Submodule.add_mem _ ?_ ?_ <;>
      · obtain ⟨f, hf⟩ := exists_ofFn_eq b
        exact Submodule.subset_span ⟨f, f, by rw [hf]; rfl⟩
  exact L.mem_stableUnits_of_val_mem_levelSpan hdiv b.length _ hval

/-- The honest transposition of two incomparable cylinders. -/
noncomputable def cylTransposition {a b : List (Fin 2)}
    (hab : ¬a <+: b) (hba : ¬b <+: a) : Aˣ :=
  L.signFlip b * L.signedSwap hab hba

theorem cylTransposition_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {a b : List (Fin 2)} (hab : ¬a <+: b) (hba : ¬b <+: a) :
    L.cylTransposition hab hba ∈ stableUnits A :=
  mul_mem (L.signFlip_mem (k := k) hdiv b) (L.signedSwap_mem hab hba)

/-- Value of the honest transposition:
`1 - p_a - p_b + s_a t_b + s_b t_a`. -/
theorem cylTransposition_val {a b : List (Fin 2)}
    (hab : ¬a <+: b) (hba : ¬b <+: a) :
    ((L.cylTransposition hab hba : Aˣ) : A) =
      1 - L.cylinder a - L.cylinder b +
        L.wordS a * L.wordT b + L.wordS b * L.wordT a := by
  show ((L.signFlip b : Aˣ) : A) *
    ((L.signedSwap hab hba : Aˣ) : A) = _
  rw [L.signedSwap_val hab hba]
  show (1 - (L.cylinder b + L.cylinder b)) * _ = _
  have hpb : L.cylinder b * L.cylinder b = L.cylinder b :=
    L.cylinder_isIdempotent b
  have hpab : L.cylinder b * L.cylinder a = 0 := by
    rw [cylinder, cylinder, show L.wordS b * L.wordT b *
      (L.wordS a * L.wordT a) =
      L.wordS b * (L.wordT b * L.wordS a) * L.wordT a from by
        noncomm_ring,
      L.wordT_mul_wordS_of_incomparable _ _ hba hab]
    noncomm_ring
  have hpsa : L.cylinder b * (L.wordS a * L.wordT b) = 0 := by
    rw [cylinder, show L.wordS b * L.wordT b *
      (L.wordS a * L.wordT b) =
      L.wordS b * (L.wordT b * L.wordS a) * L.wordT b from by
        noncomm_ring,
      L.wordT_mul_wordS_of_incomparable _ _ hba hab]
    noncomm_ring
  have hpsb : L.cylinder b * (L.wordS b * L.wordT a) =
      L.wordS b * L.wordT a := by
    rw [cylinder, show L.wordS b * L.wordT b *
      (L.wordS b * L.wordT a) =
      L.wordS b * (L.wordT b * L.wordS b) * L.wordT a from by
        noncomm_ring,
      L.wordT_mul_wordS_self]
    noncomm_ring
  calc (1 - (L.cylinder b + L.cylinder b)) *
        (1 - L.cylinder a - L.cylinder b +
          L.wordS a * L.wordT b - L.wordS b * L.wordT a)
      = (1 - L.cylinder a - L.cylinder b +
          L.wordS a * L.wordT b - L.wordS b * L.wordT a) -
        (L.cylinder b * 1 - L.cylinder b * L.cylinder a -
          L.cylinder b * L.cylinder b +
          L.cylinder b * (L.wordS a * L.wordT b) -
          L.cylinder b * (L.wordS b * L.wordT a)) -
        (L.cylinder b * 1 - L.cylinder b * L.cylinder a -
          L.cylinder b * L.cylinder b +
          L.cylinder b * (L.wordS a * L.wordT b) -
          L.cylinder b * (L.wordS b * L.wordT a)) := by
        noncomm_ring
    _ = 1 - L.cylinder a - L.cylinder b +
        L.wordS a * L.wordT b + L.wordS b * L.wordT a := by
        rw [hpb, hpab, hpsa, hpsb, mul_one]
        abel

end Scalars

end LeavittFamily
end NonsoficGroupsExist
