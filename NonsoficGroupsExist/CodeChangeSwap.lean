import NonsoficGroupsExist.CodeChangeInfrastructure

/-!
# The target-swap action on code-change sums

Multiplying a code-change sum `Σᵢ s_{tᵢ} t_{sᵢ}` on the left by the
honest transposition of two incomparable cylinders `x, y` swaps the
targets `x ↔ y` wherever they occur and fixes every target
incomparable to both — a positionless, purely elementwise computation
that drives the alignment step of the generation theorem.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- The value of a list of (target, source) pairs. -/
def pairValue (P : List (List (Fin 2) × List (Fin 2))) : A :=
  (P.map (fun p ↦ L.wordS p.1 * L.wordT p.2)).sum

@[simp] theorem pairValue_nil : L.pairValue [] = 0 := rfl

@[simp] theorem pairValue_cons (p : List (Fin 2) × List (Fin 2))
    (P : List (List (Fin 2) × List (Fin 2))) :
    L.pairValue (p :: P) =
      L.wordS p.1 * L.wordT p.2 + L.pairValue P := by
  unfold pairValue
  rw [List.map_cons, List.sum_cons]

theorem pairValue_perm {P Q : List (List (Fin 2) × List (Fin 2))}
    (h : P.Perm Q) : L.pairValue P = L.pairValue Q :=
  List.Perm.sum_eq (h.map _)

/-- The word-level swap function. -/
def swapWord (x y w : List (Fin 2)) : List (Fin 2) :=
  if w = x then y else if w = y then x else w

/-- Left multiplication by the transposition acts on a single term:
the swap on targets, provided the target is comparable to `x` or `y`
only through equality. -/
theorem cylTransposition_mul_term {x y : List (Fin 2)}
    (hxy : ¬x <+: y) (hyx : ¬y <+: x) (t s : List (Fin 2))
    (htx : t = x ∨ (¬t <+: x ∧ ¬x <+: t))
    (hty : t = y ∨ (¬t <+: y ∧ ¬y <+: t)) :
    ((L.cylTransposition hxy hyx : Aˣ) : A) *
      (L.wordS t * L.wordT s) =
    L.wordS (swapWord x y t) * L.wordT s := by
  rw [L.cylTransposition_val hxy hyx]
  have hxx : L.wordT x * L.wordS x = 1 := L.wordT_mul_wordS_self x
  have hyy : L.wordT y * L.wordS y = 1 := L.wordT_mul_wordS_self y
  have hxy0 : L.wordT y * L.wordS x = 0 :=
    L.wordT_mul_wordS_of_incomparable _ _ hyx hxy
  have hyx0 : L.wordT x * L.wordS y = 0 :=
    L.wordT_mul_wordS_of_incomparable _ _ hxy hyx
  rcases htx with rfl | htx
  · -- t = x : the term maps to `y`
    have hswap : swapWord t y t = y := by
      unfold swapWord
      rw [if_pos rfl]
    rw [hswap]
    calc (1 - L.cylinder t - L.cylinder y +
          L.wordS t * L.wordT y + L.wordS y * L.wordT t) *
          (L.wordS t * L.wordT s)
        = L.wordS t * L.wordT s -
            L.wordS t * (L.wordT t * L.wordS t) * L.wordT s -
            L.wordS y * (L.wordT y * L.wordS t) * L.wordT s +
            L.wordS t * (L.wordT y * L.wordS t) * L.wordT s +
            L.wordS y * (L.wordT t * L.wordS t) * L.wordT s := by
          rw [cylinder, cylinder]
          noncomm_ring
      _ = L.wordS y * L.wordT s := by
          rw [hxx, hxy0]
          noncomm_ring
  · rcases hty with rfl | hty
    · -- t = y : the term maps to `x`
      have hswap : swapWord x t t = x := by
        unfold swapWord
        rw [if_neg, if_pos rfl]
        intro h
        exact hyx (h ▸ List.prefix_refl x)
      rw [hswap]
      calc (1 - L.cylinder x - L.cylinder t +
            L.wordS x * L.wordT t + L.wordS t * L.wordT x) *
            (L.wordS t * L.wordT s)
          = L.wordS t * L.wordT s -
              L.wordS x * (L.wordT x * L.wordS t) * L.wordT s -
              L.wordS t * (L.wordT t * L.wordS t) * L.wordT s +
              L.wordS x * (L.wordT t * L.wordS t) * L.wordT s +
              L.wordS t * (L.wordT x * L.wordS t) * L.wordT s := by
            rw [cylinder, cylinder]
            noncomm_ring
        _ = L.wordS x * L.wordT s := by
            rw [hyy, hyx0]
            noncomm_ring
    · -- t incomparable to both : fixed
      have hswap : swapWord x y t = t := by
        unfold swapWord
        rw [if_neg, if_neg]
        · intro h
          exact hty.1 (h ▸ List.prefix_refl t)
        · intro h
          exact htx.1 (h ▸ List.prefix_refl t)
      rw [hswap]
      have htx0 : L.wordT x * L.wordS t = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ htx.2 htx.1
      have hty0 : L.wordT y * L.wordS t = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ hty.2 hty.1
      calc (1 - L.cylinder x - L.cylinder y +
            L.wordS x * L.wordT y + L.wordS y * L.wordT x) *
            (L.wordS t * L.wordT s)
          = L.wordS t * L.wordT s -
              L.wordS x * (L.wordT x * L.wordS t) * L.wordT s -
              L.wordS y * (L.wordT y * L.wordS t) * L.wordT s +
              L.wordS x * (L.wordT y * L.wordS t) * L.wordT s +
              L.wordS y * (L.wordT x * L.wordS t) * L.wordT s := by
            rw [cylinder, cylinder]
            noncomm_ring
        _ = L.wordS t * L.wordT s := by
            rw [htx0, hty0]
            noncomm_ring

/-- Left multiplication by the transposition swaps the targets of a
pair list whose targets are each equal to or incomparable with the
swapped cylinders. -/
theorem cylTransposition_mul_pairValue {x y : List (Fin 2)}
    (hxy : ¬x <+: y) (hyx : ¬y <+: x)
    (P : List (List (Fin 2) × List (Fin 2)))
    (hP : ∀ p ∈ P,
      (p.1 = x ∨ (¬p.1 <+: x ∧ ¬x <+: p.1)) ∧
      (p.1 = y ∨ (¬p.1 <+: y ∧ ¬y <+: p.1))) :
    ((L.cylTransposition hxy hyx : Aˣ) : A) * L.pairValue P =
      L.pairValue (P.map (fun p ↦ (swapWord x y p.1, p.2))) := by
  induction P with
  | nil =>
      rw [pairValue_nil, mul_zero, List.map_nil, pairValue_nil]
  | cons p P ih =>
      rw [pairValue_cons, mul_add, List.map_cons, pairValue_cons]
      have hp := hP p List.mem_cons_self
      rw [L.cylTransposition_mul_term hxy hyx p.1 p.2 hp.1 hp.2,
        ih (fun q hq ↦ hP q (List.mem_cons_of_mem p hq))]

end LeavittFamily
end NonsoficGroupsExist
