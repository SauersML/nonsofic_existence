import NonsoficGroupsExist.KOne.WindowProductClosure
import NonsoficGroupsExist.KOne.BalancedRegularity

/-!
# Nilpotent tails die: lemma (i′)

If `z` is balanced and `s₁z` is nilpotent, then any unit of value
`1 + s₁z` lies in the diagonal class group.  Induction on the
nilpotency index `D`: with `r := t₁(s₁z)^{D-1}` (pure degree `D-2`),
factor `r = R·σ` over the balanced `R := r·τ`, take a balanced
pseudo-inverse `Ξ` of `R`, and set `e := τΞr`.  Then `e(s₁z) = 0`
outright, the mover `1 - s₁(ze)` has square-zero tail (hence lies in
the diagonal class group), and it carries `z` to `z - ze` whose tail
has nilpotency index `D-1`, because `(s₁z)^{D-1}·e = s₁(re) = s₁r =
(s₁z)^{D-1}` kills the top power exactly.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- Single generators as window monomials. -/
theorem s_one_mem_window :
    L.s 1 ∈ Submodule.span k (L.degreeMonomials 1 1) :=
  Submodule.subset_span ⟨[1], [], by simp, by simp, by simp⟩

theorem t_one_mem_window :
    L.t 1 ∈ Submodule.span k (L.degreeMonomials (-1) (-1)) :=
  Submodule.subset_span ⟨[], [1], by simp, by simp, by simp⟩

theorem one_mem_window :
    (1 : A) ∈ Submodule.span k (L.degreeMonomials 0 0) :=
  Submodule.subset_span ⟨[], [], by simp, by simp, by simp⟩

theorem wordT_replicate_mem_window (d : ℕ) :
    L.wordT (List.replicate d 0) ∈
      Submodule.span k (L.degreeMonomials (-(d : ℤ)) (-(d : ℤ))) :=
  Submodule.subset_span ⟨[], List.replicate d 0, by simp, by simp,
    by simp⟩

/-- Powers of a degree-one element sit in the matching window. -/
theorem pow_mem_window {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials 1 1)) (m : ℕ) :
    x ^ m ∈ Submodule.span k (L.degreeMonomials (m : ℤ) (m : ℤ)) := by
  induction m with
  | zero =>
      rw [pow_zero]
      exact_mod_cast L.one_mem_window
  | succ m ih =>
      rw [pow_succ]
      have := L.window_mul_mem_span ih hx
      refine L.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;>
        omega

/-- **Lemma (i′): nilpotent tails die.**  If `z` is balanced and
`(s₁z)^D = 0`, every unit of value `1 + s₁z` lies in the diagonal
class group. -/
theorem nilpotent_tail_mem_stableUnits [Nontrivial A] (D : ℕ) :
    ∀ {z : A}, z ∈ Submodule.span k (L.degreeMonomials 0 0) →
    (L.s 1 * z) ^ D = 0 → ∀ u : Aˣ, (u : A) = 1 + L.s 1 * z →
    u ∈ stableUnits A := by
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro z hz hnil u hu
  rcases D with _ | _ | _ | D
  · rw [pow_zero] at hnil
    exact absurd hnil one_ne_zero
  · rw [pow_one] at hnil
    have hu1 : u = 1 := Units.ext
      (by rw [hu, hnil, add_zero, Units.val_one])
    rw [hu1]
    exact one_mem _
  · obtain ⟨n, hzn⟩ := L.span_degree_zero_le_levelSpan hz
    refine L.square_zero_tail_mem_stableUnits hzn ?_ u hu
    rw [show L.s 1 * z * (L.s 1 * z) = (L.s 1 * z) ^ 2 from by
      rw [pow_two], hnil]
  · 
      have ht1s1 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
      set nn : A := L.s 1 * z with hnn
      -- r := t₁ · n^{D+2}, pure degree D+1
      set r : A := L.t 1 * nn ^ (D + 2) with hr
      set w : List (Fin 2) := List.replicate (D + 1) 0 with hw
      set τ : A := L.wordT w with hτ
      set σ : A := L.wordS w with hσ
      have hτσ : τ * σ = 1 := L.wordT_mul_wordS_self w
      -- window memberships
      have hnwin : nn ∈ Submodule.span k (L.degreeMonomials 1 1) := by
        have := L.window_mul_mem_span (L.s_one_mem_window (k := k)) hz
        refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
      have hrwin : r ∈ Submodule.span k
          (L.degreeMonomials ((D : ℤ) + 1) ((D : ℤ) + 1)) := by
        have hp := L.pow_mem_window hnwin (D + 2)
        have := L.window_mul_mem_span (L.t_one_mem_window (k := k)) hp
        refine L.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;>
          omega
      have hτwin : τ ∈ Submodule.span k
          (L.degreeMonomials (-((D : ℤ) + 1)) (-((D : ℤ) + 1))) := by
        have := L.wordT_replicate_mem_window (k := k) (D + 1)
        refine L.span_degreeMonomials_mono ?_ ?_ this <;> push_cast <;>
          omega
      -- R := r·τ is balanced
      set R : A := r * τ with hR
      have hRwin : R ∈ Submodule.span k (L.degreeMonomials 0 0) := by
        have := L.window_mul_mem_span hrwin hτwin
        refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
      have hRσ : R * σ = r := by
        rw [hR, mul_assoc, hτσ, mul_one]
      obtain ⟨nR, hRlvl⟩ := L.span_degree_zero_le_levelSpan hRwin
      obtain ⟨Ξ, ⟨nΞ, hΞlvl⟩, hΞ⟩ :=
        L.exists_balanced_pseudoInverse hRlvl
      have hΞwin : Ξ ∈ Submodule.span k (L.degreeMonomials 0 0) :=
        L.span_levelMonomials_le_degree nΞ hΞlvl
      set e : A := τ * Ξ * r with he
      have hewin : e ∈ Submodule.span k (L.degreeMonomials 0 0) := by
        have h1 := L.window_mul_mem_span hτwin hΞwin
        have h2 := L.window_mul_mem_span h1 hrwin
        refine L.span_degreeMonomials_mono ?_ ?_ h2 <;> omega
      -- key annihilations
      have hrn : r * nn = 0 := by
        rw [hr, mul_assoc, ← pow_succ, hnil, mul_zero]
      have hen : e * nn = 0 := by
        rw [he, mul_assoc, mul_assoc, hrn]
        noncomm_ring
      have hre' : r * e = r := by
        rw [he, show r * (τ * Ξ * r) = (r * τ) * Ξ * r from by
          noncomm_ring, ← hR, ← hRσ, show R * Ξ * (R * σ) =
          (R * Ξ * R) * σ from by noncomm_ring, hΞ]
      -- the mover
      have hsqm : L.s 1 * (z * e) * (L.s 1 * (z * e)) = 0 := by
        rw [show L.s 1 * (z * e) * (L.s 1 * (z * e)) =
          L.s 1 * (z * (e * (L.s 1 * z)) * e) from by noncomm_ring,
          hen]
        noncomm_ring
      set m : Aˣ := ⟨1 - L.s 1 * (z * e), 1 + L.s 1 * (z * e),
        by
          calc (1 - L.s 1 * (z * e)) * (1 + L.s 1 * (z * e))
              = 1 - L.s 1 * (z * e) * (L.s 1 * (z * e)) := by
                noncomm_ring
            _ = 1 := by rw [hsqm, sub_zero],
        by
          calc (1 + L.s 1 * (z * e)) * (1 - L.s 1 * (z * e))
              = 1 - L.s 1 * (z * e) * (L.s 1 * (z * e)) := by
                noncomm_ring
            _ = 1 := by rw [hsqm, sub_zero]⟩ with hm
      have hzewin : z * e ∈ Submodule.span k (L.degreeMonomials 0 0)
        := by
        have := L.window_mul_mem_span hz hewin
        refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
      have hmmem : m ∈ stableUnits A := by
        obtain ⟨nze, hzelvl⟩ := L.span_degree_zero_le_levelSpan
          (Submodule.neg_mem _ hzewin)
        refine L.square_zero_tail_mem_stableUnits hzelvl ?_ m ?_
        · rw [show L.s 1 * -(z * e) * (L.s 1 * -(z * e)) =
            L.s 1 * (z * e) * (L.s 1 * (z * e)) from by noncomm_ring,
            hsqm]
        · show (1 : A) - L.s 1 * (z * e) = 1 + L.s 1 * -(z * e)
          noncomm_ring
      -- the moved unit
      have hmu : ((m * u : Aˣ) : A) = 1 + L.s 1 * (z - z * e) := by
        show (1 - L.s 1 * (z * e)) * (u : A) = _
        rw [hu]
        have hcross : L.s 1 * (z * e) * (L.s 1 * z) = 0 := by
          rw [show L.s 1 * (z * e) * (L.s 1 * z) =
            L.s 1 * (z * (e * (L.s 1 * z))) from by noncomm_ring, hen]
          noncomm_ring
        calc (1 - L.s 1 * (z * e)) * (1 + L.s 1 * z)
            = 1 + L.s 1 * (z - z * e) -
              L.s 1 * (z * e) * (L.s 1 * z) := by noncomm_ring
          _ = 1 + L.s 1 * (z - z * e) := by rw [hcross]; noncomm_ring
      have hz'win : z - z * e ∈
          Submodule.span k (L.degreeMonomials 0 0) :=
        Submodule.sub_mem _ hz hzewin
      -- index drop
      have hp1n : L.s 1 * r = nn ^ (D + 2) := by
        rw [hr, show L.s 1 * (L.t 1 * nn ^ (D + 2)) =
          (L.s 1 * L.t 1) * nn ^ (D + 2) from by noncomm_ring]
        have hpow : nn ^ (D + 2) = L.s 1 * (z * nn ^ (D + 1)) := by
          rw [show nn ^ (D + 2) = nn * nn ^ (D + 1) from by
            rw [← pow_succ']
          , hnn]
          noncomm_ring
        rw [hpow, show L.s 1 * L.t 1 * (L.s 1 * (z * nn ^ (D + 1))) =
          L.s 1 * (L.t 1 * L.s 1) * (z * nn ^ (D + 1)) from by
            noncomm_ring, ht1s1]
        noncomm_ring
      have hstep : ∀ j : ℕ, (L.s 1 * (z - z * e)) ^ (j + 1) =
          nn ^ (j + 1) - nn ^ (j + 1) * e := by
        intro j
        induction j with
        | zero =>
            rw [pow_one, pow_one, hnn]
            noncomm_ring
        | succ j ihj =>
            rw [pow_succ, ihj]
            have hexp : (nn ^ (j + 1) - nn ^ (j + 1) * e) *
                (L.s 1 * (z - z * e)) =
                nn ^ (j + 1) * nn - nn ^ (j + 1) * (nn * e) -
                  nn ^ (j + 1) * (e * nn) +
                  nn ^ (j + 1) * (e * nn) * e := by
              rw [hnn]
              noncomm_ring
            rw [hexp, hen]
            rw [show nn ^ (j + 1) * nn = nn ^ (j + 2) from by
              rw [← pow_succ]]
            noncomm_ring
      have hnil' : (L.s 1 * (z - z * e)) ^ (D + 2) = 0 := by
        rw [show D + 2 = (D + 1) + 1 from rfl, hstep (D + 1)]
        rw [show nn ^ (D + 1 + 1) = nn ^ (D + 2) from rfl]
        rw [← hp1n, mul_assoc, hre', sub_self]
      -- induction
      have hmumem := ih (D + 2) (by omega) hz'win hnil' (m * u) hmu
      have := mul_mem (inv_mem hmmem) hmumem
      rwa [inv_mul_cancel_left] at this

end LeavittFamily
end NonsoficGroupsExist
