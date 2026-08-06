import NonsoficGroupsExist.Leavitt.LeavittNormalForm

/-!
# Purely infinite simplicity of the universal binary Leavitt algebra

For every nonzero `x` in `L_k(1,2)` there are `a` and `b` with
`a * x * b = 1`.  The proof needs no basis theorem: writing `x` in the
monomial spanning family, a right multiplication by a suitable `s_δ`
collapses the `t`-side (if all such products vanished, the cylinder
partition of unity would force `x = 0`); a left multiplication by the
`t`-word of a minimal-length surviving monomial produces a unit constant
plus a tail of proper `s`-monomials; and conjugating by the aperiodic
word `0^m 1` annihilates the tail.
-/

namespace NonsoficGroupsExist

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The cylinder partition of unity at every depth. -/
theorem sum_cylinder_ofFn (r : ℕ) :
    ∑ f : Fin r → Fin 2, L.cylinder (List.ofFn f) = 1 := by
  induction r with
  | zero => simp [cylinder]
  | succ r ih =>
      have hsplit : ∀ (i : Fin 2) (f : Fin r → Fin 2),
          L.cylinder (List.ofFn (Fin.cons i f : Fin (r + 1) → Fin 2)) =
            L.s i * L.cylinder (List.ofFn f) * L.t i := by
        intro i f
        have hlist : List.ofFn (Fin.cons i f : Fin (r + 1) → Fin 2) =
            i :: List.ofFn f := by
          simp [List.ofFn_succ]
        rw [hlist]
        unfold cylinder
        rw [wordS_cons, wordT_cons]
        simp only [mul_assoc]
      calc
        (∑ f : Fin (r + 1) → Fin 2, L.cylinder (List.ofFn f)) =
            ∑ p : Fin 2 × (Fin r → Fin 2),
              L.cylinder (List.ofFn
                (Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2)) :=
          (Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ Fin 2))
            (fun p ↦ L.cylinder (List.ofFn
              (Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2)))
            (fun f ↦ L.cylinder (List.ofFn f))
            (fun p ↦ rfl)).symm
        _ = ∑ i : Fin 2, ∑ f : Fin r → Fin 2,
            L.cylinder (List.ofFn (Fin.cons i f : Fin (r + 1) → Fin 2)) :=
          Fintype.sum_prod_type _
        _ = ∑ i : Fin 2, L.s i * L.t i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          calc
            (∑ f : Fin r → Fin 2, L.cylinder
                (List.ofFn (Fin.cons i f : Fin (r + 1) → Fin 2))) =
                L.s i * (∑ f : Fin r → Fin 2,
                  L.cylinder (List.ofFn f)) * L.t i := by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun f _ ↦ hsplit i f
            _ = L.s i * L.t i := by rw [ih, mul_one]
        _ = 1 := by
          rw [Fin.sum_univ_two]
          exact L.sum_s_mul_t

/-- Reconstruction of any element from its depth-`r` corners. -/
theorem eq_sum_mul_wordS_mul_wordT (x : A) (r : ℕ) :
    x = ∑ f : Fin r → Fin 2,
      x * L.wordS (List.ofFn f) * L.wordT (List.ofFn f) := by
  calc
    x = x * ∑ f : Fin r → Fin 2, L.cylinder (List.ofFn f) := by
      rw [sum_cylinder_ofFn, mul_one]
    _ = ∑ f : Fin r → Fin 2,
        x * L.wordS (List.ofFn f) * L.wordT (List.ofFn f) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      unfold cylinder
      rw [mul_assoc]

end LeavittFamily

namespace BinaryLeavitt

open LeavittFamily

/-- The aperiodic annihilating word `0^m 1`. -/
def killWord (m : ℕ) : List (Fin 2) := List.replicate m 0 ++ [1]

theorem killWord_length (m : ℕ) : (killWord m).length = m + 1 := by
  simp [killWord]

/-- `0^m 1` is not a prefix of `ε ++ 0^m 1` for `1 ≤ |ε| ≤ m`: the two
words disagree at position `m`. -/
theorem killWord_not_prefix (ε : List (Fin 2)) (m : ℕ)
    (hne : ε ≠ []) (hlen : ε.length ≤ m) :
    ¬ (killWord m <+: ε ++ killWord m) := by
  intro hpre
  have hεpos : 0 < ε.length := List.length_pos_iff.mpr hne
  have hklen : (killWord m).length = m + 1 := killWord_length m
  have hm1 : m < (killWord m).length := by omega
  have hm2 : m < (ε ++ killWord m).length := by
    rw [List.length_append]
    omega
  have hagree : (killWord m)[m]'hm1 = (ε ++ killWord m)[m]'hm2 :=
    hpre.getElem hm1
  have hlast : (killWord m)[m]'hm1 = 1 := by
    unfold killWord
    rw [List.getElem_append_right (by simp)]
    simp
  have hmid : (ε ++ killWord m)[m]'hm2 = 0 := by
    rw [List.getElem_append_right (by omega)]
    unfold killWord
    rw [List.getElem_append_left (by
      rw [List.length_replicate]
      omega)]
    simp
  rw [hlast, hmid] at hagree
  exact absurd hagree (by decide)

variable (k : Type) [Field k]

/-- Every element of `L_k(1,2)` has a finite monomial representation. -/
theorem exists_monomial_representation (x : BinaryLeavittAlgebra k) :
    ∃ (n : ℕ) (co : Fin n → k) (al be : Fin n → List (Fin 2)),
      x = ∑ i, co i •
        ((family k).wordS (al i) * (family k).wordT (be i)) := by
  have hx : x ∈ Submodule.span k (monomialSet k) := by
    rw [span_monomialSet_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, rfl⟩ := hu
      exact ⟨1, fun _ ↦ 1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨n₁, co₁, al₁, be₁, rfl⟩ := hu
      obtain ⟨n₂, co₂, al₂, be₂, rfl⟩ := hv
      refine ⟨n₁ + n₂, Fin.append co₁ co₂, Fin.append al₁ al₂,
        Fin.append be₁ be₂, ?_⟩
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ ↦ by
          rw [Fin.append_left, Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ ↦ by
          rw [Fin.append_right, Fin.append_right, Fin.append_right]
  | smul c u _ hu =>
      obtain ⟨n, co, al, be, rfl⟩ := hu
      refine ⟨n, fun i ↦ c * co i, al, be, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ ↦
        smul_smul c (co i)
          ((family k).wordS (al i) * (family k).wordT (be i))

open Classical in
/-- **Purely infinite simplicity in the strong two-sided form**
(checkpoint `B2`): every nonzero element of `L_k(1,2)` divides the
identity from both sides. -/
theorem exists_mul_mul_eq_one
    {x : BinaryLeavittAlgebra k} (hx : x ≠ 0) :
    ∃ a b : BinaryLeavittAlgebra k, a * x * b = 1 := by
  set L := family k with hL
  obtain ⟨n, co, al, be, hrep⟩ := exists_monomial_representation k x
  -- collapse the `t`-side by a right corner
  set M := Finset.univ.sup (fun i : Fin n ↦ (be i).length) with hM
  have hnonvanish : ∃ f : Fin M → Fin 2,
      x * L.wordS (List.ofFn f) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    rw [eq_sum_mul_wordS_mul_wordT L x M]
    refine Finset.sum_eq_zero fun f _ ↦ ?_
    rw [hall f, zero_mul]
  obtain ⟨f₀, hy0⟩ := hnonvanish
  set δ := List.ofFn f₀ with hδ
  have hδlen : δ.length = M := by
    rw [hδ, List.length_ofFn]
  set y := x * L.wordS δ with hy
  -- the collapsed element is a combination of pure `s`-monomials
  set T := Finset.univ.filter (fun i : Fin n ↦ be i <+: δ) with hT
  set γfun : Fin n → List (Fin 2) :=
    fun i ↦ al i ++ δ.drop (be i).length with hγfun
  have hyrep : y = ∑ i ∈ T, co i • L.wordS (γfun i) := by
    rw [hy, hrep, Finset.sum_mul]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n ↦ be i <+: δ)]
    rw [show (∑ i ∈ Finset.univ.filter
        (fun i : Fin n ↦ ¬ be i <+: δ),
        (co i • (L.wordS (al i) * L.wordT (be i))) * L.wordS δ) =
      0 from Finset.sum_eq_zero fun i hi ↦ by
        rw [Finset.mem_filter] at hi
        have hnotrev : ¬ δ <+: be i := by
          intro hrev
          have hlen : δ.length ≤ (be i).length := hrev.length_le
          have hlen2 : (be i).length ≤ M := by
            rw [hM]
            exact Finset.le_sup (f := fun i : Fin n ↦ (be i).length)
              (Finset.mem_univ i)
          have heq : δ.length = (be i).length := by omega
          have : δ = be i := List.IsPrefix.eq_of_length hrev heq
          exact hi.2 (this ▸ List.prefix_refl δ)
        rw [smul_mul_assoc, mul_assoc,
          L.wordT_mul_wordS_of_incomparable (be i) δ hi.2 hnotrev,
          mul_zero, smul_zero]]
    rw [add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hT, Finset.mem_filter] at hi
    obtain ⟨e, he⟩ := hi.2
    have hdrop : δ.drop (be i).length = e := by
      rw [← he, List.drop_left]
    have hγ : γfun i = al i ++ e := by
      rw [hγfun]
      beta_reduce
      rw [hdrop]
    have hcollapse : L.wordT (be i) * L.wordS δ = L.wordS e := by
      rw [← he]
      exact L.wordT_mul_wordS_append_left (be i) e
    rw [hγ, smul_mul_assoc, mul_assoc, hcollapse, L.wordS_append]
  -- regroup equal `s`-words
  set G := T.image γfun with hG
  set g : List (Fin 2) → k :=
    fun γ ↦ ∑ i ∈ T.filter (fun i ↦ γfun i = γ), co i with hg
  have hydisj : ((G : Set (List (Fin 2)))).PairwiseDisjoint
      (fun γ ↦ T.filter (fun i ↦ γfun i = γ)) := by
    intro γ₁ _ γ₂ _ hne
    refine Finset.disjoint_left.2 fun i h1 h2 ↦ ?_
    rw [Finset.mem_filter] at h1 h2
    exact hne (h1.2 ▸ h2.2)
  have hybiunion : G.biUnion
      (fun γ ↦ T.filter (fun i ↦ γfun i = γ)) = T := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, hG,
      Finset.mem_image]
    constructor
    · rintro ⟨γ, -, hi, -⟩
      exact hi
    · intro hi
      exact ⟨γfun i, ⟨i, hi, rfl⟩, hi, rfl⟩
  have hyreg : y = ∑ γ ∈ G, g γ • L.wordS γ := by
    rw [hyrep, ← hybiunion, Finset.sum_biUnion hydisj]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [hg]
    beta_reduce
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  -- keep only the surviving groups
  set G' := G.filter (fun γ ↦ g γ ≠ 0) with hG'
  have hyreg' : y = ∑ γ ∈ G', g γ • L.wordS γ := by
    rw [hyreg, hG']
    rw [← Finset.sum_filter_add_sum_filter_not G (fun γ ↦ g γ ≠ 0)]
    rw [show (∑ γ ∈ G.filter (fun γ ↦ ¬ g γ ≠ 0),
        g γ • L.wordS γ) = 0 from Finset.sum_eq_zero fun γ hγ ↦ by
      rw [Finset.mem_filter] at hγ
      rw [not_not.mp hγ.2, zero_smul]]
    rw [add_zero]
  have hG'ne : G'.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hy0
    rw [hyreg', hempty, Finset.sum_empty]
  obtain ⟨γ₀, hγ₀G, hγ₀min⟩ :=
    Finset.exists_min_image G' List.length hG'ne
  have hgγ₀ : g γ₀ ≠ 0 := (Finset.mem_filter.mp hγ₀G).2
  -- the annihilating conjugation
  set m := G'.sup List.length with hm
  set w := killWord m with hw
  have hkill : ∀ γ ∈ G'.erase γ₀,
      L.wordT w * (L.wordT γ₀ * L.wordS γ) * L.wordS w = 0 := by
    intro γ hγ
    have hγG' : γ ∈ G' := Finset.mem_of_mem_erase hγ
    have hγne : γ ≠ γ₀ := Finset.ne_of_mem_erase hγ
    have hminle : γ₀.length ≤ γ.length := hγ₀min γ hγG'
    by_cases hpre : γ₀ <+: γ
    · obtain ⟨ε, hε⟩ := hpre
      have hεne : ε ≠ [] := by
        rintro rfl
        rw [List.append_nil] at hε
        exact hγne hε.symm
      have hεlen : ε.length ≤ m := by
        have hγlen : γ.length ≤ m := Finset.le_sup hγG'
        have := congrArg List.length hε
        rw [List.length_append] at this
        omega
      rw [← hε, L.wordT_mul_wordS_append_left γ₀ ε]
      rw [show L.wordT w * L.wordS ε * L.wordS w =
        L.wordT w * L.wordS (ε ++ w) from by
        rw [L.wordS_append, mul_assoc]]
      rw [L.wordT_mul_wordS_of_incomparable w (ε ++ w)
        (killWord_not_prefix ε m hεne hεlen)
        (by
          intro hrev
          have := hrev.length_le
          rw [List.length_append] at this
          have : ε.length = 0 := by omega
          exact hεne (List.length_eq_zero_iff.mp this))]
    · have hnotrev : ¬ γ <+: γ₀ := by
        intro hrev
        have hlen : γ.length ≤ γ₀.length := hrev.length_le
        have heq : γ.length = γ₀.length := by omega
        exact hγne (List.IsPrefix.eq_of_length hrev heq)
      rw [L.wordT_mul_wordS_of_incomparable γ₀ γ hpre hnotrev,
        mul_zero, zero_mul]
  have hcollapse : L.wordT w * (L.wordT γ₀ * y) * L.wordS w =
      g γ₀ • 1 := by
    calc
      L.wordT w * (L.wordT γ₀ * y) * L.wordS w =
          ∑ γ ∈ G', L.wordT w * (L.wordT γ₀ * (g γ • L.wordS γ)) *
            L.wordS w := by
        rw [hyreg', Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      _ = g γ₀ • 1 := by
        rw [Finset.sum_eq_single_of_mem γ₀ hγ₀G (fun γ hγ hne ↦ by
          rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc,
            hkill γ (Finset.mem_erase.2 ⟨hne, hγ⟩), smul_zero])]
        rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc,
          L.wordT_mul_wordS_self, mul_one, L.wordT_mul_wordS_self]
  refine ⟨(g γ₀)⁻¹ • (L.wordT w * L.wordT γ₀),
    L.wordS δ * L.wordS w, ?_⟩
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [show L.wordT w * L.wordT γ₀ * x * (L.wordS δ * L.wordS w) =
    L.wordT w * (L.wordT γ₀ * y) * L.wordS w from by
    rw [hy]
    simp only [mul_assoc]]
  rw [hcollapse, smul_smul, inv_mul_cancel₀ hgγ₀, one_smul]

end BinaryLeavitt

end NonsoficGroupsExist
