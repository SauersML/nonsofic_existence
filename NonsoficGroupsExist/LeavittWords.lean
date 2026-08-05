import NonsoficGroupsExist.Leavitt
import Mathlib.Data.List.Infix
import Mathlib.Tactic.NoncommRing

/-!
# Leaf calculus

This file formalizes Lemma `lem:leaf` of the manuscript over an arbitrary ring
carrying a binary Leavitt family: the word maps `α ↦ s_α` and `α ↦ t_α`, their
orthogonality relations, and the cylinder projections `p_α = s_α t_α` together
with the splitting `p_α = p_{α0} + p_{α1}`.

Everything below is a finite computation from the two defining relations, so it
applies verbatim to `L_k(1,2)` for every `k` and to every unital ring containing
a binary Leavitt family.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The two prefixing operators, indexed uniformly. -/
def s : Fin 2 → A := ![L.s0, L.s1]

/-- The two deletion operators, indexed uniformly. -/
def t : Fin 2 → A := ![L.t0, L.t1]

@[simp] theorem s_zero : L.s 0 = L.s0 := rfl
@[simp] theorem s_one : L.s 1 = L.s1 := rfl
@[simp] theorem t_zero : L.t 0 = L.t0 := rfl
@[simp] theorem t_one : L.t 1 = L.t1 := rfl

@[simp] theorem t_mul_s (i j : Fin 2) :
    L.t i * L.s j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [s, t]

theorem sum_s_mul_t : L.s 0 * L.t 0 + L.s 1 * L.t 1 = 1 := L.sum_range

/-- `s_α` for a finite binary word `α`. -/
def wordS : List (Fin 2) → A
  | [] => 1
  | i :: a => L.s i * wordS a

/-- `t_α` for a finite binary word `α`. -/
def wordT : List (Fin 2) → A
  | [] => 1
  | i :: a => wordT a * L.t i

@[simp] theorem wordS_nil : L.wordS [] = 1 := rfl
@[simp] theorem wordT_nil : L.wordT [] = 1 := rfl
@[simp] theorem wordS_cons (i : Fin 2) (a : List (Fin 2)) :
    L.wordS (i :: a) = L.s i * L.wordS a := rfl
@[simp] theorem wordT_cons (i : Fin 2) (a : List (Fin 2)) :
    L.wordT (i :: a) = L.wordT a * L.t i := rfl

theorem wordS_append (a b : List (Fin 2)) :
    L.wordS (a ++ b) = L.wordS a * L.wordS b := by
  induction a with
  | nil => simp
  | cons i a ih => simp [ih, mul_assoc]

theorem wordT_append (a b : List (Fin 2)) :
    L.wordT (a ++ b) = L.wordT b * L.wordT a := by
  induction a with
  | nil => simp
  | cons i a ih => simp [ih, mul_assoc]

/-- **Lemma `lem:leaf`(i)**: `t_α s_α = 1`. -/
theorem wordT_mul_wordS_self (a : List (Fin 2)) :
    L.wordT a * L.wordS a = 1 := by
  induction a with
  | nil => simp
  | cons i a ih =>
      calc
        L.wordT (i :: a) * L.wordS (i :: a) =
            L.wordT a * ((L.t i * L.s i) * L.wordS a) := by
          simp only [wordT_cons, wordS_cons, mul_assoc]
        _ = 1 := by simp [ih]

/-- **Lemma `lem:leaf`(ii)**: `t_α s_β = 0` for incomparable words. -/
theorem wordT_mul_wordS_of_incomparable (a b : List (Fin 2))
    (hab : ¬a <+: b) (hba : ¬b <+: a) : L.wordT a * L.wordS b = 0 := by
  induction a generalizing b with
  | nil => exact (hab (by simp)).elim
  | cons i a ih =>
      cases b with
      | nil => exact (hba (by simp)).elim
      | cons j b =>
          by_cases hij : i = j
          · subst j
            have hab' : ¬a <+: b := by
              intro hp
              exact hab (by simpa using hp)
            have hba' : ¬b <+: a := by
              intro hp
              exact hba (by simpa using hp)
            calc
              L.wordT (i :: a) * L.wordS (i :: b) =
                  L.wordT a * ((L.t i * L.s i) * L.wordS b) := by
                simp only [wordT_cons, wordS_cons, mul_assoc]
              _ = L.wordT a * L.wordS b := by simp
              _ = 0 := ih b hab' hba'
          · calc
              L.wordT (i :: a) * L.wordS (j :: b) =
                  L.wordT a * ((L.t i * L.s j) * L.wordS b) := by
                simp only [wordT_cons, wordS_cons, mul_assoc]
              _ = 0 := by simp [hij]

/-- The cylinder projection `p_α = s_α t_α`. -/
def cylinder (a : List (Fin 2)) : A := L.wordS a * L.wordT a

theorem cylinder_isIdempotent (a : List (Fin 2)) :
    L.cylinder a * L.cylinder a = L.cylinder a := by
  unfold cylinder
  calc
    (L.wordS a * L.wordT a) * (L.wordS a * L.wordT a) =
        L.wordS a * (L.wordT a * L.wordS a) * L.wordT a := by noncomm_ring
    _ = L.wordS a * L.wordT a := by rw [wordT_mul_wordS_self]; simp

theorem cylinder_mul_of_incomparable (a b : List (Fin 2))
    (hab : ¬a <+: b) (hba : ¬b <+: a) :
    L.cylinder a * L.cylinder b = 0 := by
  unfold cylinder
  calc
    (L.wordS a * L.wordT a) * (L.wordS b * L.wordT b) =
        L.wordS a * (L.wordT a * L.wordS b) * L.wordT b := by noncomm_ring
    _ = 0 := by rw [wordT_mul_wordS_of_incomparable L a b hab hba]; simp

/-- **Lemma `lem:leaf`(iii)**: the binary splitting of a cylinder. -/
theorem cylinder_split (a : List (Fin 2)) :
    L.cylinder a = L.cylinder (a ++ [0]) + L.cylinder (a ++ [1]) := by
  calc
    L.cylinder a = L.wordS a * (L.s 0 * L.t 0 + L.s 1 * L.t 1) * L.wordT a := by
      rw [sum_s_mul_t]
      simp [cylinder]
    _ = L.cylinder (a ++ [0]) + L.cylinder (a ++ [1]) := by
      simp [cylinder, wordS_append, wordT_append, mul_add, add_mul, mul_assoc]

/-- Every prefix matrix coefficient splits simultaneously along its two
binary children. -/
theorem wordS_mul_wordT_split (a b : List (Fin 2)) :
    L.wordS a * L.wordT b =
      L.wordS (a ++ [0]) * L.wordT (b ++ [0]) +
        L.wordS (a ++ [1]) * L.wordT (b ++ [1]) := by
  calc
    L.wordS a * L.wordT b =
        L.wordS a * (L.s 0 * L.t 0 + L.s 1 * L.t 1) * L.wordT b := by
      rw [L.sum_s_mul_t]
      simp
    _ = L.wordS (a ++ [0]) * L.wordT (b ++ [0]) +
        L.wordS (a ++ [1]) * L.wordT (b ++ [1]) := by
      simp [wordS_append, wordT_append, mul_add, add_mul, mul_assoc]

/-- The splitting of the prefixing operator, used by the compressor identities
of Section `subsec:compressor`. -/
theorem wordS_split (a : List (Fin 2)) :
    L.wordS a = L.wordS (a ++ [0]) * L.t 0 + L.wordS (a ++ [1]) * L.t 1 := by
  calc
    L.wordS a = L.wordS a * (L.s 0 * L.t 0 + L.s 1 * L.t 1) := by
      rw [sum_s_mul_t]; simp
    _ = L.wordS (a ++ [0]) * L.t 0 + L.wordS (a ++ [1]) * L.t 1 := by
      simp [wordS_append, mul_add, mul_assoc]

theorem wordT_split (a : List (Fin 2)) :
    L.wordT a = L.s 0 * L.wordT (a ++ [0]) + L.s 1 * L.wordT (a ++ [1]) := by
  calc
    L.wordT a = (L.s 0 * L.t 0 + L.s 1 * L.t 1) * L.wordT a := by
      rw [sum_s_mul_t]; simp
    _ = L.s 0 * L.wordT (a ++ [0]) + L.s 1 * L.wordT (a ++ [1]) := by
      simp [wordT_append, add_mul, mul_assoc]

/-- Words with a common prefix stay incomparable when the prefix is removed. -/
theorem not_prefix_append_left (l a b : List (Fin 2)) (hab : ¬a <+: b) :
    ¬ l ++ a <+: l ++ b := by
  intro h
  exact hab (by simpa using h)

/-- Incomparable words remain incomparable after arbitrary extension. -/
theorem not_prefix_append_right (a b x y : List (Fin 2))
    (hab : ¬a <+: b) (hba : ¬b <+: a) : ¬ a ++ x <+: b ++ y := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hle : a.length ≤ b.length
  · exact hab ((List.isPrefix_append_of_length hle).mp ha)
  · apply hba
    rw [List.prefix_iff_eq_take]
    have hea := List.prefix_iff_eq_take.mp ha
    rw [hea, List.take_take, Nat.min_eq_left (Nat.le_of_not_ge hle)]
    simp


/-- Collapse of a left prefix: `t_α · s_{αγ} = s_γ`. -/
theorem wordT_mul_wordS_append_left (a e : List (Fin 2)) :
    L.wordT a * L.wordS (a ++ e) = L.wordS e := by
  rw [wordS_append, ← mul_assoc, wordT_mul_wordS_self, one_mul]

/-- Collapse of a right prefix: `t_{αγ} · s_α = t_γ`. -/
theorem wordT_append_mul_wordS (a f : List (Fin 2)) :
    L.wordT (a ++ f) * L.wordS a = L.wordT f := by
  rw [wordT_append, mul_assoc, wordT_mul_wordS_self, mul_one]

end LeavittFamily
end NonsoficGroupsExist
