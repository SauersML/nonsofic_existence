import NonsoficGroupsExist.WidthTwoReduction
import NonsoficGroupsExist.IncomparableUnipotents

/-!
# Pure positive tails die: the block-move induction

Every unit of the binary Leavitt algebra of the form `1 + τ` with `τ`
of pure positive degrees `[1, N]` lies in the diagonal class group.
The induction peels the top degree: writing the top component as
`η = s₀(t₀η) + s₁(t₁η)`, the depth-two corner embedding
`κ(v) = 1 + s₀₀ τ t₀₀` is squeezed between two products of
incomparable unipotents; the cross terms collapse through the
complete depth-two code and produce a unit with tail of degrees
`[1, N-1]` — the depth-one corner picture of the stable Whitehead
block move `diag(u, I) ~ [[u - PQ, -P], [Q, I]]`.  The base case is
the width-two reduction.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Pure positive tails die.** -/
theorem pure_positive_tail_mem_stableUnits
    [Nontrivial (BinaryLeavittAlgebra k)] :
    ∀ (N : ℕ) {τ : BinaryLeavittAlgebra k},
      τ ∈ Submodule.span k
        ((family k).degreeMonomials 1 ((N : ℤ) + 1)) →
      ∀ u : (BinaryLeavittAlgebra k)ˣ,
        (u : BinaryLeavittAlgebra k) = 1 + τ →
        u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  intro N
  induction N with
  | zero =>
      intro τ hτ u hu
      refine window_zero_one_mem_stableUnits k u ?_
      rw [hu]
      -- `one_mem_window` lands in the window `0 0`; the target is `0 1`.
      refine Submodule.add_mem _
        (L.span_degreeMonomials_mono (by omega) (by omega)
          (L.one_mem_window (k := k))) ?_
      exact L.span_degreeMonomials_mono (by omega) (by omega) hτ
  | succ N ih =>
      intro τ hτ u hu
      rw [show (((N + 1 : ℕ) : ℤ) + 1) = (N : ℤ) + 2 from by
        push_cast; ring] at hτ
      -- split off the top component
      obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k hτ
      set η : BinaryLeavittAlgebra k := y ((N : ℤ) + 2) with hη
      set a : BinaryLeavittAlgebra k :=
        ∑ d ∈ Finset.Icc (1 : ℤ) ((N : ℤ) + 1), y d with ha
      have hτsplit : τ = a + η := by
        rw [hysum, ha, hη]
        have hins : Finset.Icc (1 : ℤ) ((N : ℤ) + 2) =
            insert ((N : ℤ) + 2) (Finset.Icc (1 : ℤ) ((N : ℤ) + 1))
            := by
          ext d
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hins, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), add_comm]
      have haw : a ∈ Submodule.span k
          (L.degreeMonomials 1 ((N : ℤ) + 1)) := by
        rw [ha]
        refine Submodule.sum_mem _ fun d hd ↦ ?_
        have hd' := Finset.mem_Icc.mp hd
        exact L.span_degreeMonomials_mono (by omega) (by omega)
          (hymem d)
      have hηw : η ∈ Submodule.span k
          (L.degreeMonomials ((N : ℤ) + 2) ((N : ℤ) + 2)) := hymem _
      -- the two branch coefficients of the top component
      set q₀ : BinaryLeavittAlgebra k := L.t 0 * η with hq₀
      set q₁ : BinaryLeavittAlgebra k := L.t 1 * η with hq₁
      have hsplitη : L.s 0 * q₀ + L.s 1 * q₁ = η := by
        rw [hq₀, hq₁, ← mul_assoc, ← mul_assoc, ← add_mul,
          L.sum_s_mul_t, one_mul]
      have ht0w : L.t 0 ∈ Submodule.span k
          (L.degreeMonomials (-1) (-1)) :=
        Submodule.subset_span ⟨[], [0], by simp, by simp, by simp⟩
      have ht1w : L.t 1 ∈ Submodule.span k
          (L.degreeMonomials (-1) (-1)) :=
        Submodule.subset_span ⟨[], [1], by simp, by simp, by simp⟩
      have hq₀w : q₀ ∈ Submodule.span k
          (L.degreeMonomials ((N : ℤ) + 1) ((N : ℤ) + 1)) := by
        have h1 := L.window_mul_mem_span (k := k) ht0w hηw
        refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
      have hq₁w : q₁ ∈ Submodule.span k
          (L.degreeMonomials ((N : ℤ) + 1) ((N : ℤ) + 1)) := by
        have h1 := L.window_mul_mem_span (k := k) ht1w hηw
        refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
      -- the corner embedding at the word 00
      have hts : L.wordT [0, 0] * L.wordS [0, 0] = 1 :=
        L.wordT_mul_wordS_self [0, 0]
      set κ : (BinaryLeavittAlgebra k)ˣ :=
        pairKappaUnit (L.wordS [0, 0]) (L.wordT [0, 0]) hts u with hκ
      have hκmem : κ * u⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) :=
        pairKappaUnit_mul_inv_mem_stableUnits _ _ hts hdiv u
      have hκval : (κ : BinaryLeavittAlgebra k) =
          1 + L.wordS [0, 0] * τ * L.wordT [0, 0] := by
        show L.wordS [0, 0] * (u : BinaryLeavittAlgebra k) *
            L.wordT [0, 0] +
          (1 - L.wordS [0, 0] * L.wordT [0, 0]) = _
        rw [hu]
        have h1 : L.wordS [0, 0] * (1 + τ) * L.wordT [0, 0] =
            L.wordS [0, 0] * L.wordT [0, 0] +
            L.wordS [0, 0] * τ * L.wordT [0, 0] := by noncomm_ring
        rw [h1]
        noncomm_ring
      -- the four unipotent factors
      have hinc₁ : ¬[(0 : Fin 2), 0] <+: [(0 : Fin 2), 1] := by decide
      have hinc₁' : ¬[(0 : Fin 2), 1] <+: [(0 : Fin 2), 0] := by decide
      have hinc₂ : ¬[(0 : Fin 2), 0] <+: [(1 : Fin 2), 0] := by decide
      have hinc₂' : ¬[(1 : Fin 2), 0] <+: [(0 : Fin 2), 0] := by decide
      set X₀ : BinaryLeavittAlgebra k :=
        L.wordS [0, 0] * L.s 0 * L.wordT [0, 1] with hX₀
      set X₁ : BinaryLeavittAlgebra k :=
        L.wordS [0, 0] * L.s 1 * L.wordT [1, 0] with hX₁
      set Y₀ : BinaryLeavittAlgebra k :=
        L.wordS [0, 1] * q₀ * L.wordT [0, 0] with hY₀
      set Y₁ : BinaryLeavittAlgebra k :=
        L.wordS [1, 0] * q₁ * L.wordT [0, 0] with hY₁
      set K : BinaryLeavittAlgebra k :=
        L.wordS [0, 0] * τ * L.wordT [0, 0] with hK
      -- vanishing between blocks
      have hz₁ : L.wordT [0, 1] * L.wordS [0, 0] = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ hinc₁' hinc₁
      have hz₂ : L.wordT [1, 0] * L.wordS [0, 0] = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ hinc₂' hinc₂
      have hz₃ : L.wordT [0, 0] * L.wordS [0, 1] = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ hinc₁ hinc₁'
      have hz₄ : L.wordT [0, 0] * L.wordS [1, 0] = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ hinc₂ hinc₂'
      have hone₁ : L.wordT [0, 1] * L.wordS [0, 1] = 1 :=
        L.wordT_mul_wordS_self _
      have hone₂ : L.wordT [1, 0] * L.wordS [1, 0] = 1 :=
        L.wordT_mul_wordS_self _
      -- the products that survive
      have hXY : X₀ * Y₀ + X₁ * Y₁ =
          L.wordS [0, 0] * η * L.wordT [0, 0] := by
        rw [hX₀, hY₀, hX₁, hY₁]
        rw [show L.wordS [0, 0] * L.s 0 * L.wordT [0, 1] *
            (L.wordS [0, 1] * q₀ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 0 *
            (L.wordT [0, 1] * L.wordS [0, 1]) * q₀ * L.wordT [0, 0]
          from by noncomm_ring, hone₁]
        rw [show L.wordS [0, 0] * L.s 1 * L.wordT [1, 0] *
            (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 1 *
            (L.wordT [1, 0] * L.wordS [1, 0]) * q₁ * L.wordT [0, 0]
          from by noncomm_ring, hone₂]
        rw [show L.wordS [0, 0] * L.s 0 * 1 * q₀ * L.wordT [0, 0] +
            L.wordS [0, 0] * L.s 1 * 1 * q₁ * L.wordT [0, 0] =
          L.wordS [0, 0] * (L.s 0 * q₀ + L.s 1 * q₁) * L.wordT [0, 0]
          from by noncomm_ring, hsplitη]
      have hXKfactsA : X₀ * K = 0 := by
        rw [hX₀, hK, show L.wordS [0, 0] * L.s 0 * L.wordT [0, 1] *
          (L.wordS [0, 0] * τ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 0 *
            (L.wordT [0, 1] * L.wordS [0, 0]) * τ * L.wordT [0, 0]
          from by noncomm_ring, hz₁]
        noncomm_ring
      have hXKfactsB : X₁ * K = 0 := by
        rw [hX₁, hK, show L.wordS [0, 0] * L.s 1 * L.wordT [1, 0] *
          (L.wordS [0, 0] * τ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 1 *
            (L.wordT [1, 0] * L.wordS [0, 0]) * τ * L.wordT [0, 0]
          from by noncomm_ring, hz₂]
        noncomm_ring
      have hKYfactsA : K * Y₀ = 0 := by
        rw [hY₀, hK, show L.wordS [0, 0] * τ * L.wordT [0, 0] *
          (L.wordS [0, 1] * q₀ * L.wordT [0, 0]) =
          L.wordS [0, 0] * τ *
            (L.wordT [0, 0] * L.wordS [0, 1]) * q₀ * L.wordT [0, 0]
          from by noncomm_ring, hz₃]
        noncomm_ring
      have hKYfactsB : K * Y₁ = 0 := by
        rw [hY₁, hK, show L.wordS [0, 0] * τ * L.wordT [0, 0] *
          (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) =
          L.wordS [0, 0] * τ *
            (L.wordT [0, 0] * L.wordS [1, 0]) * q₁ * L.wordT [0, 0]
          from by noncomm_ring, hz₄]
        noncomm_ring
      -- the two class-group multipliers
      set m₂ : (BinaryLeavittAlgebra k)ˣ :=
        L.incomparableUnit hinc₁ hinc₁' (-(L.s 0)) *
          L.incomparableUnit hinc₂ hinc₂' (-(L.s 1)) with hm₂
      set m₁ : (BinaryLeavittAlgebra k)ˣ :=
        L.incomparableUnit hinc₁' hinc₁ q₀ *
          L.incomparableUnit hinc₂' hinc₂ q₁ with hm₁
      have hm₂mem : m₂ ∈ stableUnits (BinaryLeavittAlgebra k) :=
        mul_mem (L.incomparableUnit_mem hinc₁ hinc₁' _)
          (L.incomparableUnit_mem hinc₂ hinc₂' _)
      have hm₁mem : m₁ ∈ stableUnits (BinaryLeavittAlgebra k) :=
        mul_mem (L.incomparableUnit_mem hinc₁' hinc₁ _)
          (L.incomparableUnit_mem hinc₂' hinc₂ _)
      have hm₂val : (m₂ : BinaryLeavittAlgebra k) = 1 - X₀ - X₁ := by
        show (1 + L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1]) *
          (1 + L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0]) = _
        have hcross : L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1] *
            (L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0]) = 0 := by
          rw [show L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1] *
            (L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0]) =
            L.wordS [0, 0] * (-(L.s 0)) *
              (L.wordT [0, 1] * L.wordS [0, 0]) * (-(L.s 1)) *
              L.wordT [1, 0] from by noncomm_ring, hz₁]
          noncomm_ring
        calc (1 + L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1]) *
              (1 + L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0])
            = 1 + L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1] +
              L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0] +
              L.wordS [0, 0] * (-(L.s 0)) * L.wordT [0, 1] *
                (L.wordS [0, 0] * (-(L.s 1)) * L.wordT [1, 0]) := by
              noncomm_ring
          _ = 1 - X₀ - X₁ := by
              rw [hcross, hX₀, hX₁]
              noncomm_ring
      have hm₁val : (m₁ : BinaryLeavittAlgebra k) = 1 + Y₀ + Y₁ := by
        show (1 + L.wordS [0, 1] * q₀ * L.wordT [0, 0]) *
          (1 + L.wordS [1, 0] * q₁ * L.wordT [0, 0]) = _
        have hcross : L.wordS [0, 1] * q₀ * L.wordT [0, 0] *
            (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) = 0 := by
          rw [show L.wordS [0, 1] * q₀ * L.wordT [0, 0] *
            (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) =
            L.wordS [0, 1] * q₀ *
              (L.wordT [0, 0] * L.wordS [1, 0]) * q₁ * L.wordT [0, 0]
            from by noncomm_ring, hz₄]
          noncomm_ring
        calc (1 + L.wordS [0, 1] * q₀ * L.wordT [0, 0]) *
              (1 + L.wordS [1, 0] * q₁ * L.wordT [0, 0])
            = 1 + L.wordS [0, 1] * q₀ * L.wordT [0, 0] +
              L.wordS [1, 0] * q₁ * L.wordT [0, 0] +
              L.wordS [0, 1] * q₀ * L.wordT [0, 0] *
                (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) := by
              noncomm_ring
          _ = 1 + Y₀ + Y₁ := by
              rw [hcross, hY₀, hY₁]
              noncomm_ring
      -- the block-move product and its value
      set u' : (BinaryLeavittAlgebra k)ˣ := m₂ * κ * m₁ with hu'
      have hXY₀₁ : X₀ * Y₁ = 0 := by
        rw [hX₀, hY₁, show L.wordS [0, 0] * L.s 0 * L.wordT [0, 1] *
          (L.wordS [1, 0] * q₁ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 0 *
            (L.wordT [0, 1] * L.wordS [1, 0]) * q₁ * L.wordT [0, 0]
          from by noncomm_ring,
          L.wordT_mul_wordS_of_incomparable _ _ (by decide) (by decide)]
        noncomm_ring
      have hXY₁₀ : X₁ * Y₀ = 0 := by
        rw [hX₁, hY₀, show L.wordS [0, 0] * L.s 1 * L.wordT [1, 0] *
          (L.wordS [0, 1] * q₀ * L.wordT [0, 0]) =
          L.wordS [0, 0] * L.s 1 *
            (L.wordT [1, 0] * L.wordS [0, 1]) * q₀ * L.wordT [0, 0]
          from by noncomm_ring,
          L.wordT_mul_wordS_of_incomparable _ _ (by decide) (by decide)]
        noncomm_ring
      have hu'val : (u' : BinaryLeavittAlgebra k) =
          1 + (L.wordS [0, 0] * a * L.wordT [0, 0] - X₀ - X₁ +
            Y₀ + Y₁) := by
        show (m₂ : BinaryLeavittAlgebra k) *
          (κ : BinaryLeavittAlgebra k) *
          (m₁ : BinaryLeavittAlgebra k) = _
        rw [hm₂val, hκval, hm₁val, ← hK]
        calc (1 - X₀ - X₁) * (1 + K) * (1 + Y₀ + Y₁)
            = 1 + K + Y₀ + Y₁ + K * Y₀ + K * Y₁ - X₀ - X₁ -
              X₀ * K - X₁ * K - X₀ * Y₀ - X₀ * Y₁ - X₁ * Y₀ -
              X₁ * Y₁ - X₀ * K * Y₀ - X₀ * K * Y₁ - X₁ * K * Y₀ -
              X₁ * K * Y₁ := by noncomm_ring
          _ = 1 + K + Y₀ + Y₁ - X₀ - X₁ - (X₀ * Y₀ + X₁ * Y₁) := by
              rw [hKYfactsA, hKYfactsB, hXKfactsA, hXKfactsB,
                hXY₀₁, hXY₁₀]
              rw [show X₀ * K * Y₀ = 0 from by
                  rw [hXKfactsA]; noncomm_ring,
                show X₀ * K * Y₁ = 0 from by
                  rw [hXKfactsA]; noncomm_ring,
                show X₁ * K * Y₀ = 0 from by
                  rw [hXKfactsB]; noncomm_ring,
                show X₁ * K * Y₁ = 0 from by
                  rw [hXKfactsB]; noncomm_ring]
              noncomm_ring
          _ = 1 + (L.wordS [0, 0] * a * L.wordT [0, 0] - X₀ - X₁ +
              Y₀ + Y₁) := by
              rw [hXY, hK, hτsplit]
              noncomm_ring
      -- the new tail lives one degree lower
      have hs00w : L.wordS [0, 0] ∈ Submodule.span k
          (L.degreeMonomials 2 2) :=
        Submodule.subset_span ⟨[0, 0], [], by simp, by simp, by simp⟩
      have ht00w : L.wordT [0, 0] ∈ Submodule.span k
          (L.degreeMonomials (-2) (-2)) :=
        Submodule.subset_span ⟨[], [0, 0], by simp, by simp, by simp⟩
      have hs01w : L.wordS [0, 1] ∈ Submodule.span k
          (L.degreeMonomials 2 2) :=
        Submodule.subset_span ⟨[0, 1], [], by simp, by simp, by simp⟩
      have hs10w : L.wordS [1, 0] ∈ Submodule.span k
          (L.degreeMonomials 2 2) :=
        Submodule.subset_span ⟨[1, 0], [], by simp, by simp, by simp⟩
      have htail : L.wordS [0, 0] * a * L.wordT [0, 0] - X₀ - X₁ +
          Y₀ + Y₁ ∈ Submodule.span k
          (L.degreeMonomials 1 ((N : ℤ) + 1)) := by
        refine Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_) ?_
        · have h1 := L.window_mul_mem_span (k := k)
            (L.window_mul_mem_span (k := k) hs00w haw) ht00w
          refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
        -- Pin the intermediate window to `1 1` explicitly.  Feeding
        -- `subset_span` straight into `span_degreeMonomials_mono` leaves
        -- `lo`/`hi` as metavariables, so neither the `simp`s nor the
        -- `omega`s have anything to solve against.
        · have hx₀ : X₀ ∈ Submodule.span k (L.degreeMonomials 1 1) := by
            rw [hX₀]
            refine Submodule.subset_span
              ⟨[0, 0, 0], [0, 1], by simp, by simp, ?_⟩
            rw [show ([0, 0, 0] : List (Fin 2)) = [0, 0] ++ [0] from
              rfl, L.wordS_append]
            simp [wordS]
          exact L.span_degreeMonomials_mono (by omega) (by omega) hx₀
        · have hx₁ : X₁ ∈ Submodule.span k (L.degreeMonomials 1 1) := by
            rw [hX₁]
            refine Submodule.subset_span
              ⟨[0, 0, 1], [1, 0], by simp, by simp, ?_⟩
            rw [show ([0, 0, 1] : List (Fin 2)) = [0, 0] ++ [1] from
              rfl, L.wordS_append]
            simp [wordS]
          exact L.span_degreeMonomials_mono (by omega) (by omega) hx₁
        · rw [hY₀]
          have h1 := L.window_mul_mem_span (k := k)
            (L.window_mul_mem_span (k := k) hs01w hq₀w) ht00w
          refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
        · rw [hY₁]
          have h1 := L.window_mul_mem_span (k := k)
            (L.window_mul_mem_span (k := k) hs10w hq₁w) ht00w
          refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
      -- close the induction
      have hu'mem : u' ∈ stableUnits (BinaryLeavittAlgebra k) := by
        rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · subst hN0
          refine window_zero_one_mem_stableUnits k u' ?_
          rw [hu'val]
          refine Submodule.add_mem _
            (L.span_degreeMonomials_mono (by omega) (by omega)
              (L.one_mem_window (k := k))) ?_
          exact L.span_degreeMonomials_mono (by omega) (by omega)
            htail
        · exact ih (τ := L.wordS [0, 0] * a * L.wordT [0, 0] -
            X₀ - X₁ + Y₀ + Y₁) htail u' hu'val
      -- assemble: u = (κ·u⁻¹)⁻¹-free form
      have hassemble : u = (κ * u⁻¹)⁻¹ * (m₂⁻¹ * u' * m₁⁻¹) := by
        rw [hu']
        group
      rw [hassemble]
      exact mul_mem (inv_mem hκmem)
        (mul_mem (mul_mem (inv_mem hm₂mem) hu'mem) (inv_mem hm₁mem))

end BinaryLeavitt
end NonsoficGroupsExist
