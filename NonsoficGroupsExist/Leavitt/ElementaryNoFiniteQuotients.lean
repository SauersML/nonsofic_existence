import NonsoficGroupsExist.Leavitt.ElementaryGroup
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Elementary groups over infinite rings with strong division have no finite quotients

Every negative statement about the witness so far -- not sofic, hence not LEF,
hence not residually finite -- says that some approximation *fails*.  This file
proves a positive structural fact in the opposite direction, and it is much
stronger than the failure of residual finiteness: for a ring `R` that is
infinite and in which every nonzero element divides `1` on both sides, and at
least three indices, *every* homomorphism from `EL_ι(R)` to a finite group is
trivial.  There is no residual structure for the failure of soficity to hide
behind, because there is none at all.

The proof is three commutators and a division.

* Fix `i ≠ j`.  Because `x_{ij}` turns addition into multiplication, the set
  `a ↦ φ(x_{ij}(a))` is a homomorphism from `(R,+)`, so if no nonzero `a` were
  killed it would be injective and `R` would embed in a finite group
  (`exists_ne_zero_mem_elementaryKernel`).
* Steinberg moves that one killed `a` into every other root subgroup:
  `[x_{ij}(a), x_{jk}(b)] = x_{ik}(ab)` kills `ab`, and
  `[x_{li}(c), x_{ik}(ab)] = x_{lk}(cab)` kills `cab`.
* Strong division closes it.  Given `u a v = 1`, every `d` factors as
  `(du) a v`, so the second step kills *all* of `R` in the target root
  subgroup, not merely an ideal's worth of it.

The index bookkeeping is the only fiddly part, and it is what forces three
indices: to reach a prescribed pair `(l, k)` one takes `i ∉ {l, k}` and `j = l`.
-/

namespace NonsoficGroupsExist

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- An elementary matrix, packaged as an element of `EL_ι(R)` itself. -/
def elGen (i j : ι) (h : i ≠ j) (a : R) : elementaryGroup ι R :=
  ⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩

@[simp] theorem elGen_zero (i j : ι) (h : i ≠ j) :
    elGen (R := R) i j h 0 = 1 :=
  Subtype.ext (elementaryUnit_zero i j h)

theorem elGen_mul (i j : ι) (h : i ≠ j) (a b : R) :
    elGen i j h a * elGen i j h b = elGen (R := R) i j h (a + b) :=
  Subtype.ext (elementaryUnit_mul i j h a b)

/-- The Steinberg relation, inside `EL_ι(R)` and with the commutator written
out: the bracket notation is not available on the subgroup. -/
theorem elGen_commutator (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    elGen i j hij a * elGen j k hjk b * (elGen i j hij a)⁻¹ * (elGen j k hjk b)⁻¹
      = elGen (R := R) i k hik (a * b) :=
  Subtype.ext (elementaryUnit_commutator i j k hij hjk hik a b)

variable {Q : Type*} [Group Q]

/-- **Some nonzero element is killed.**  Otherwise `a ↦ φ(x_{ij}(a))` is
injective and the infinite ring `R` embeds into the finite group `Q`. -/
theorem exists_ne_zero_mem_elementaryKernel [Infinite R] [Finite Q]
    (φ : elementaryGroup ι R →* Q) (i j : ι) (h : i ≠ j) :
    ∃ a : R, a ≠ 0 ∧ φ (elGen i j h a) = 1 := by
  by_contra hcon
  have hinj : Function.Injective fun a : R ↦ φ (elGen i j h a) := by
    intro a b hab
    by_contra hne
    refine hcon ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
    have hsum : elGen i j h (a - b) * elGen i j h b = elGen (R := R) i j h a := by
      rw [elGen_mul, sub_add_cancel]
    have hmap := congrArg φ hsum
    rw [map_mul] at hmap
    have hab' : φ (elGen i j h a) = φ (elGen i j h b) := hab
    rw [hab'] at hmap
    have : φ (elGen i j h (a - b)) * φ (elGen i j h b)
        = 1 * φ (elGen i j h b) := by rw [hmap, one_mul]
    exact mul_right_cancel this
  have : Finite R := Finite.of_injective _ hinj
  exact not_finite R

/-- **Every finite quotient of `EL_ι(R)` is trivial**, for `R` infinite with
strong two-sided division and at least three indices.  The three indices enter
only through the pair of Steinberg commutators. -/
theorem elementaryGroup_finite_quotient_trivial [Infinite R] [Finite Q]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ u v : R, u * x * v = 1)
    (hthree : ∀ l k : ι, l ≠ k → ∃ i : ι, i ≠ l ∧ i ≠ k)
    (φ : elementaryGroup ι R →* Q) (g : elementaryGroup ι R) :
    φ g = 1 := by
  -- every generator dies
  have hgen : ∀ (l k : ι) (h : l ≠ k) (d : R), φ (elGen l k h d) = 1 := by
    intro l k hlk d
    obtain ⟨i, hil, hik⟩ := hthree l k hlk
    -- the pair `(i, l)` supplies a nonzero killed element
    have hil' : i ≠ l := hil
    obtain ⟨a, ha0, ha⟩ := exists_ne_zero_mem_elementaryKernel φ i l hil'
    obtain ⟨u, v, huv⟩ := hdiv a ha0
    -- first commutator: `a * b` dies in the `(i, k)` subgroup
    have step₁ : ∀ b : R, φ (elGen i k hik (a * b)) = 1 := by
      intro b
      rw [← elGen_commutator i l k hil' hlk hik a b, map_mul, map_mul, map_mul,
        map_inv, map_inv, ha]
      simp
    -- second commutator: `c * (a * b)` dies in the `(l, k)` subgroup
    have step₂ : ∀ b c : R, φ (elGen l k hlk (c * (a * b))) = 1 := by
      intro b c
      rw [← elGen_commutator l i k (Ne.symm hil') hik hlk c (a * b), map_mul,
        map_mul, map_mul, map_inv, map_inv, step₁ b]
      simp
    -- strong division: every `d` is such a product
    have hfactor : d = (d * u) * (a * v) := by
      calc d = d * (u * a * v) := by rw [huv, mul_one]
        _ = (d * u) * (a * v) := by simp [mul_assoc]
    rw [hfactor]
    exact step₂ v (d * u)
  -- and the generators generate
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨l, k, hlk, d, rfl⟩ := hx
      exact hgen l k hlk d
  | one => exact map_one φ
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : elementaryGroup ι R)
          = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, ihx, ihy, one_mul]
  | inv x hx ihx =>
      have : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : elementaryGroup ι R) = (⟨x, hx⟩)⁻¹ := rfl
      rw [this, map_inv, ihx, inv_one]

/-- Three distinct indices are available whenever there are at least three. -/
theorem exists_third_index (h : 3 ≤ Fintype.card ι) (l k : ι) :
    ∃ i : ι, i ≠ l ∧ i ≠ k := by
  classical
  by_contra hcon
  have hsub : (Finset.univ : Finset ι) ⊆ {l, k} := by
    intro x _
    by_contra hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact hcon ⟨x, fun hl ↦ hx (Or.inl hl), fun hk ↦ hx (Or.inr hk)⟩
  have hcard : Fintype.card ι ≤ 2 := by
    calc Fintype.card ι = (Finset.univ : Finset ι).card := (Finset.card_univ).symm
      _ ≤ ({l, k} : Finset ι).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  omega

end NonsoficGroupsExist
