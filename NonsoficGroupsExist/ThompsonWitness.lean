import NonsoficGroupsExist.LeavittWords
import NonsoficGroupsExist.Scheme

/-!
# The explicit Thompson witness

The non-LEF criterion of `ThompsonObstruction` needs two concrete noncommuting
units satisfying the two Thompson relations.  This file constructs them inside
the unit group of any ring carrying a binary Leavitt family, using only prefix
transpositions of cylinders:

* `cylinderSwap a b` -- the involution exchanging two incomparable cylinders;
* `prefixInsertion l` -- the embedding `u ↦ s_l u t_l + (1 - p_l)` of the unit
  group into the corner at the cylinder `l`;
* `generatorA`, `generatorB` -- the two units of the witness, with
  `generatorB = prefixInsertion [1] generatorA`;
* `relator_one`, `relator_two`, `generators_not_commute` -- the two Thompson
  relations and the failure of commutation.

The mechanism is the one used in the manuscript: the two relations hold because
the difference `a b⁻¹` acts as the identity on the cylinder supporting the
conjugated generator, and conjugation by an element acting on words transports
the insertion homomorphism from one cylinder to another.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-! ### Cylinder transpositions -/

/-- The transposition value `1 - p_a - p_b + s_a t_b + s_b t_a`. -/
def transpositionValue (sa ta sb tb : A) : A :=
  1 - sa * ta - sb * tb + sa * tb + sb * ta

theorem transpositionValue_mul_self (sa ta sb tb : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0) :
    transpositionValue sa ta sb tb * transpositionValue sa ta sb tb = 1 := by
  have haa' (x : A) : ta * (sa * x) = x := by rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by rw [← mul_assoc, hba, zero_mul]
  unfold transpositionValue
  noncomm_ring [haa, hbb, hab, hba, haa', hbb', hab', hba']

/-- The involution exchanging the cylinders of two incomparable words. -/
def cylinderSwap (a b : List (Fin 2)) (hab : ¬a <+: b) (hba : ¬b <+: a) : Aˣ where
  val := transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b)
  inv := transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b)
  val_inv :=
    transpositionValue_mul_self _ _ _ _
      (L.wordT_mul_wordS_self a) (L.wordT_mul_wordS_self b)
      (L.wordT_mul_wordS_of_incomparable a b hab hba)
      (L.wordT_mul_wordS_of_incomparable b a hba hab)
  inv_val :=
    transpositionValue_mul_self _ _ _ _
      (L.wordT_mul_wordS_self a) (L.wordT_mul_wordS_self b)
      (L.wordT_mul_wordS_of_incomparable a b hab hba)
      (L.wordT_mul_wordS_of_incomparable b a hba hab)

@[simp] theorem cylinderSwap_val (a b : List (Fin 2)) (hab : ¬a <+: b)
    (hba : ¬b <+: a) :
    (↑(L.cylinderSwap a b hab hba) : A) =
      transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) := rfl

/-! ### Prefix insertion -/

/-- The unit `s_l u t_l + (1 - p_l)`, acting as `u` inside the cylinder `l` and
as the identity outside it. -/
def prefixInsertionUnit (l : List (Fin 2)) (u : Aˣ) : Aˣ where
  val := L.wordS l * (↑u : A) * L.wordT l + (1 - L.cylinder l)
  inv := L.wordS l * (↑(u⁻¹) : A) * L.wordT l + (1 - L.cylinder l)
  val_inv := by
    have hTS := L.wordT_mul_wordS_self l
    have hTS' (x : A) : L.wordT l * (L.wordS l * x) = x := by
      rw [← mul_assoc, hTS, one_mul]
    have hc : L.cylinder l = L.wordS l * L.wordT l := rfl
    have huu : (↑u : A) * (↑(u⁻¹) : A) = 1 := by
      exact Units.mul_inv u
    noncomm_ring [hc, hTS, hTS', huu]
    rw [← mul_assoc (↑u : A) (↑(u⁻¹) : A) (L.wordT l), huu, one_mul]
    abel
  inv_val := by
    have hTS := L.wordT_mul_wordS_self l
    have hTS' (x : A) : L.wordT l * (L.wordS l * x) = x := by
      rw [← mul_assoc, hTS, one_mul]
    have hc : L.cylinder l = L.wordS l * L.wordT l := rfl
    have huu : (↑(u⁻¹) : A) * (↑u : A) = 1 := by
      exact Units.inv_mul u
    noncomm_ring [hc, hTS, hTS', huu]
    rw [← mul_assoc (↑(u⁻¹) : A) (↑u : A) (L.wordT l), huu, one_mul]
    abel

@[simp] theorem prefixInsertionUnit_val (l : List (Fin 2)) (u : Aˣ) :
    (↑(L.prefixInsertionUnit l u) : A) =
      L.wordS l * (↑u : A) * L.wordT l + (1 - L.cylinder l) := rfl

theorem prefixInsertionUnit_one (l : List (Fin 2)) :
    L.prefixInsertionUnit l 1 = 1 := by
  apply Units.ext
  change L.wordS l * (1 : A) * L.wordT l + (1 - L.cylinder l) = 1
  have hc : L.cylinder l = L.wordS l * L.wordT l := rfl
  rw [hc]
  noncomm_ring

theorem prefixInsertionUnit_mul (l : List (Fin 2)) (u v : Aˣ) :
    L.prefixInsertionUnit l (u * v) =
      L.prefixInsertionUnit l u * L.prefixInsertionUnit l v := by
  apply Units.ext
  have hTS := L.wordT_mul_wordS_self l
  have hTS' (x : A) : L.wordT l * (L.wordS l * x) = x := by
    rw [← mul_assoc, hTS, one_mul]
  have hc : L.cylinder l = L.wordS l * L.wordT l := rfl
  change L.wordS l * ((↑u : A) * (↑v : A)) * L.wordT l + (1 - L.cylinder l) =
    (L.wordS l * (↑u : A) * L.wordT l + (1 - L.cylinder l)) *
      (L.wordS l * (↑v : A) * L.wordT l + (1 - L.cylinder l))
  noncomm_ring [hc, hTS, hTS']

/-- Prefix insertion as a homomorphism of unit groups. -/
def prefixInsertion (l : List (Fin 2)) : Aˣ →* Aˣ where
  toFun := L.prefixInsertionUnit l
  map_one' := L.prefixInsertionUnit_one l
  map_mul' := L.prefixInsertionUnit_mul l

@[simp] theorem prefixInsertion_apply (l : List (Fin 2)) (u : Aˣ) :
    L.prefixInsertion l u = L.prefixInsertionUnit l u := rfl

/-! ### Word actions -/

/-- A unit *acts* on words by carrying the cylinder `a` onto the cylinder `b`. -/
structure PrefixWordAction (g : Aˣ) (a b : List (Fin 2)) : Prop where
  prefixing : (↑g : A) * L.wordS a = L.wordS b
  deletion : L.wordT a * (↑(g⁻¹) : A) = L.wordT b

theorem PrefixWordAction.inv {g : Aˣ} {a b : List (Fin 2)}
    (h : L.PrefixWordAction g a b) : L.PrefixWordAction g⁻¹ b a := by
  have hunit : (↑g⁻¹ : A) * (↑g : A) = 1 := by
    exact Units.inv_mul g
  constructor
  · calc
      (↑g⁻¹ : A) * L.wordS b = (↑g⁻¹ : A) * ((↑g : A) * L.wordS a) := by
        rw [h.prefixing]
      _ = L.wordS a := by rw [← mul_assoc, hunit, one_mul]
  · change L.wordT b * (↑g : A) = L.wordT a
    calc
      L.wordT b * (↑g : A) = (L.wordT a * (↑g⁻¹ : A)) * (↑g : A) := by
        rw [h.deletion]
      _ = L.wordT a := by rw [mul_assoc, hunit, mul_one]

theorem PrefixWordAction.mul {g h : Aˣ} {a b c : List (Fin 2)}
    (hg : L.PrefixWordAction g b c) (hh : L.PrefixWordAction h a b) :
    L.PrefixWordAction (g * h) a c := by
  constructor
  · change ((↑g : A) * (↑h : A)) * L.wordS a = L.wordS c
    rw [mul_assoc, hh.prefixing, hg.prefixing]
  · change L.wordT a * ((↑(h⁻¹) : A) * (↑(g⁻¹) : A)) = L.wordT c
    rw [← mul_assoc, hh.deletion, hg.deletion]

theorem PrefixWordAction.append {g : Aˣ} {a b : List (Fin 2)}
    (h : L.PrefixWordAction g a b) (r : List (Fin 2)) :
    L.PrefixWordAction g (a ++ r) (b ++ r) := by
  constructor
  · rw [wordS_append, wordS_append, ← mul_assoc, h.prefixing]
  · rw [wordT_append, wordT_append, mul_assoc, h.deletion]

/-- Prefix insertion transports a word action into the indicated cylinder. -/
theorem prefixInsertion_action {g : Aˣ} {a b : List (Fin 2)}
    (h : L.PrefixWordAction g a b) (l : List (Fin 2)) :
    L.PrefixWordAction (L.prefixInsertion l g) (l ++ a) (l ++ b) := by
  have hTS := L.wordT_mul_wordS_self l
  have hTS' (x : A) : L.wordT l * (L.wordS l * x) = x := by
    rw [← mul_assoc, hTS, one_mul]
  have hc : L.cylinder l = L.wordS l * L.wordT l := rfl
  constructor
  · rw [wordS_append, wordS_append]
    change
      (L.wordS l * (↑g : A) * L.wordT l + (1 - L.cylinder l)) *
          (L.wordS l * L.wordS a) =
        L.wordS l * L.wordS b
    rw [hc]
    calc
      (L.wordS l * (↑g : A) * L.wordT l +
            (1 - L.wordS l * L.wordT l)) *
          (L.wordS l * L.wordS a) =
          L.wordS l * ((↑g : A) * L.wordS a) := by
            noncomm_ring [hTS]
            simp only [hTS']
            abel
      _ = L.wordS l * L.wordS b := by rw [h.prefixing]
  · rw [wordT_append, wordT_append]
    change
      (L.wordT a * L.wordT l) *
          (L.wordS l * (↑g⁻¹ : A) * L.wordT l + (1 - L.cylinder l)) =
        L.wordT b * L.wordT l
    rw [hc]
    calc
      (L.wordT a * L.wordT l) *
          (L.wordS l * (↑g⁻¹ : A) * L.wordT l +
            (1 - L.wordS l * L.wordT l)) =
          (L.wordT a * (↑g⁻¹ : A)) * L.wordT l := by
            noncomm_ring [hTS]
            simp only [hTS']
            abel
      _ = L.wordT b * L.wordT l := by rw [h.deletion]

theorem cylinderSwap_action_left (a b : List (Fin 2)) (hab : ¬a <+: b)
    (hba : ¬b <+: a) : L.PrefixWordAction (L.cylinderSwap a b hab hba) a b := by
  have haa := L.wordT_mul_wordS_self a
  have hbb := L.wordT_mul_wordS_self b
  have hab' := L.wordT_mul_wordS_of_incomparable a b hab hba
  have hba' := L.wordT_mul_wordS_of_incomparable b a hba hab
  have haa' (x : A) : L.wordT a * (L.wordS a * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hab'' (x : A) : L.wordT a * (L.wordS b * x) = 0 := by
    rw [← mul_assoc, hab', zero_mul]
  constructor
  · change transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) *
      L.wordS a = L.wordS b
    unfold transpositionValue
    noncomm_ring [haa, hbb, hab', hba']
  · change L.wordT a *
      transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) =
      L.wordT b
    unfold transpositionValue
    noncomm_ring [haa, hab', haa', hab'']

theorem cylinderSwap_action_right (a b : List (Fin 2)) (hab : ¬a <+: b)
    (hba : ¬b <+: a) : L.PrefixWordAction (L.cylinderSwap a b hab hba) b a := by
  have hswap : L.cylinderSwap a b hab hba = L.cylinderSwap b a hba hab := by
    apply Units.ext
    change transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) =
      transpositionValue (L.wordS b) (L.wordT b) (L.wordS a) (L.wordT a)
    unfold transpositionValue
    noncomm_ring
  rw [hswap]
  exact L.cylinderSwap_action_left b a hba hab

theorem cylinderSwap_action_fixed (a b w : List (Fin 2)) (hab : ¬a <+: b)
    (hba : ¬b <+: a) (haw : ¬a <+: w) (hwa : ¬w <+: a) (hbw : ¬b <+: w)
    (hwb : ¬w <+: b) : L.PrefixWordAction (L.cylinderSwap a b hab hba) w w := by
  have haw' := L.wordT_mul_wordS_of_incomparable a w haw hwa
  have hbw' := L.wordT_mul_wordS_of_incomparable b w hbw hwb
  have hwa' := L.wordT_mul_wordS_of_incomparable w a hwa haw
  have hwb' := L.wordT_mul_wordS_of_incomparable w b hwb hbw
  have hwa'' (x : A) : L.wordT w * (L.wordS a * x) = 0 := by
    rw [← mul_assoc, hwa', zero_mul]
  have hwb'' (x : A) : L.wordT w * (L.wordS b * x) = 0 := by
    rw [← mul_assoc, hwb', zero_mul]
  constructor
  · change transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) *
      L.wordS w = L.wordS w
    unfold transpositionValue
    noncomm_ring [haw', hbw']
  · change L.wordT w *
      transpositionValue (L.wordS a) (L.wordT a) (L.wordS b) (L.wordT b) =
      L.wordT w
    unfold transpositionValue
    noncomm_ring [hwa', hwb', hwa'', hwb'']

/-- Conjugating a prefix insertion by a unit that carries `a` to `b` moves the
insertion from the cylinder `a` to the cylinder `b`. -/
theorem prefixInsertion_conjugate {g : Aˣ} {a b : List (Fin 2)}
    (h : L.PrefixWordAction g a b) (u : Aˣ) :
    g * L.prefixInsertion a u * g⁻¹ = L.prefixInsertion b u := by
  apply Units.ext
  have hunit : (↑g : A) * (↑g⁻¹ : A) = 1 := by
    exact Units.mul_inv g
  have hca : L.cylinder a = L.wordS a * L.wordT a := rfl
  have hcb : L.cylinder b = L.wordS b * L.wordT b := rfl
  change (↑g : A) *
      (L.wordS a * (↑u : A) * L.wordT a + (1 - L.cylinder a)) * (↑g⁻¹ : A) =
    L.wordS b * (↑u : A) * L.wordT b + (1 - L.cylinder b)
  calc
    (↑g : A) * (L.wordS a * (↑u : A) * L.wordT a + (1 - L.cylinder a)) *
        (↑g⁻¹ : A) =
        ((↑g : A) * L.wordS a) * (↑u : A) * (L.wordT a * (↑g⁻¹ : A)) +
          ((↑g : A) * (↑g⁻¹ : A) -
            ((↑g : A) * L.wordS a) * (L.wordT a * (↑g⁻¹ : A))) := by
      rw [hca]; noncomm_ring
    _ = L.wordS b * (↑u : A) * L.wordT b + (1 - L.cylinder b) := by
      rw [h.prefixing, h.deletion, hunit, hcb]

/-- A unit acting trivially on a cylinder commutes with every insertion into
that cylinder. -/
theorem commute_prefixInsertion_of_fixed {g : Aˣ} {w : List (Fin 2)}
    (h : L.PrefixWordAction g w w) (u : Aˣ) :
    Commute g (L.prefixInsertion w u) := by
  have hconj := L.prefixInsertion_conjugate h u
  apply (commute_iff_eq _ _).2
  calc
    g * L.prefixInsertion w u = (g * L.prefixInsertion w u * g⁻¹) * g := by group
    _ = L.prefixInsertion w u * g := by rw [hconj]

/-! ### The witness -/

/-- The rotation exchanging the three cylinders `[0]`, `[1,0]`, `[1,1]`. -/
def rootRotation : Aˣ :=
  L.cylinderSwap [0] [1, 0] (by decide) (by decide) *
    L.cylinderSwap [0] [1, 1] (by decide) (by decide) *
    L.cylinderSwap [0] [1] (by decide) (by decide)

/-- The same rotation inserted into the cylinder `[1]`. -/
def rightRotation : Aˣ := L.prefixInsertion [1] L.rootRotation

/-- The first generator of the witness. -/
def generatorA : Aˣ := (L.rootRotation)⁻¹

/-- The second generator of the witness. -/
def generatorB : Aˣ := (L.rightRotation)⁻¹

theorem rootRotation_action_zero_one :
    L.PrefixWordAction L.rootRotation [0, 1] [1, 0] := by
  unfold rootRotation
  rw [mul_assoc]
  refine PrefixWordAction.mul L (b := [0]) ?_ ?_
  · exact L.cylinderSwap_action_left [0] [1, 0] (by decide) (by decide)
  · refine PrefixWordAction.mul L (b := [1, 1]) ?_ ?_
    · exact L.cylinderSwap_action_right [0] [1, 1] (by decide) (by decide)
    · exact PrefixWordAction.append L
        (L.cylinderSwap_action_left [0] [1] (by decide) (by decide)) [1]

theorem rootRotation_action_one :
    L.PrefixWordAction L.rootRotation [1] [1, 1] := by
  unfold rootRotation
  rw [mul_assoc]
  refine PrefixWordAction.mul L (b := [1, 1]) ?_ ?_
  · exact L.cylinderSwap_action_fixed [0] [1, 0] [1, 1] (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · refine PrefixWordAction.mul L (b := [0]) ?_ ?_
    · exact L.cylinderSwap_action_left [0] [1, 1] (by decide) (by decide)
    · exact L.cylinderSwap_action_right [0] [1] (by decide) (by decide)

theorem generatorB_eq_prefixInsertion :
    L.generatorB = L.prefixInsertion [1] L.generatorA := by
  change (L.prefixInsertion [1] L.rootRotation)⁻¹ =
    L.prefixInsertion [1] (L.rootRotation)⁻¹
  exact ((L.prefixInsertion [1]).map_inv L.rootRotation).symm

/-- The first conjugate of the second generator is an insertion at `[1,1]`. -/
theorem generator_conjugate_one :
    (L.generatorA)⁻¹ * L.generatorB * L.generatorA =
      L.prefixInsertion [1, 1] L.generatorA := by
  calc
    (L.generatorA)⁻¹ * L.generatorB * L.generatorA =
        L.rootRotation * L.prefixInsertion [1] L.generatorA *
          (L.rootRotation)⁻¹ := by
      rw [generatorB_eq_prefixInsertion]
      simp [generatorA]
    _ = L.prefixInsertion [1, 1] L.generatorA :=
      L.prefixInsertion_conjugate L.rootRotation_action_one L.generatorA

/-- The second conjugate is an insertion at `[1,1,1]`. -/
theorem generator_conjugate_two :
    ((L.generatorA) ^ 2)⁻¹ * L.generatorB * (L.generatorA) ^ 2 =
      L.prefixInsertion [1, 1, 1] L.generatorA := by
  have hrot : L.PrefixWordAction L.rootRotation [1, 1] [1, 1, 1] := by
    exact PrefixWordAction.append L L.rootRotation_action_one [1]
  calc
    ((L.generatorA) ^ 2)⁻¹ * L.generatorB * (L.generatorA) ^ 2 =
        L.rootRotation * ((L.generatorA)⁻¹ * L.generatorB * L.generatorA) *
          (L.rootRotation)⁻¹ := by
      simp [generatorA, pow_two, mul_assoc]
    _ = L.rootRotation * L.prefixInsertion [1, 1] L.generatorA *
          (L.rootRotation)⁻¹ := by rw [generator_conjugate_one]
    _ = L.prefixInsertion [1, 1, 1] L.generatorA :=
      L.prefixInsertion_conjugate hrot L.generatorA

/-- The difference of the two generators fixes the cylinder `[1,1]`. -/
theorem generator_difference_fixes :
    L.PrefixWordAction (L.generatorA * (L.generatorB)⁻¹) [1, 1] [1, 1] := by
  have hrot : L.PrefixWordAction L.rootRotation [1, 1] [1, 1, 1] := by
    exact PrefixWordAction.append L L.rootRotation_action_one [1]
  have hright : L.PrefixWordAction L.rightRotation [1, 1] [1, 1, 1] :=
    L.prefixInsertion_action L.rootRotation_action_one [1]
  change L.PrefixWordAction ((L.rootRotation)⁻¹ * ((L.rightRotation)⁻¹)⁻¹) [1, 1] [1, 1]
  simp only [inv_inv]
  exact PrefixWordAction.mul L (PrefixWordAction.inv L hrot) hright

/-- **The first Thompson relation.** -/
theorem relator_one :
    Commute (L.generatorA * (L.generatorB)⁻¹)
      ((L.generatorA)⁻¹ * L.generatorB * L.generatorA) := by
  rw [generator_conjugate_one]
  exact L.commute_prefixInsertion_of_fixed L.generator_difference_fixes L.generatorA

/-- **The second Thompson relation.** -/
theorem relator_two :
    Commute (L.generatorA * (L.generatorB)⁻¹)
      (((L.generatorA) ^ 2)⁻¹ * L.generatorB * (L.generatorA) ^ 2) := by
  rw [generator_conjugate_two]
  apply L.commute_prefixInsertion_of_fixed _ L.generatorA
  exact PrefixWordAction.append L L.generator_difference_fixes [1]

/-- The two generators do not commute: they move the word `[1,1,0]` to
incomparable words. -/
theorem generators_not_commute [Nontrivial A] :
    ¬ Commute L.generatorA L.generatorB := by
  have hazero : L.PrefixWordAction L.generatorA [1, 0] [0, 1] :=
    PrefixWordAction.inv L L.rootRotation_action_zero_one
  have haone : L.PrefixWordAction L.generatorA [1, 1] [1] :=
    PrefixWordAction.inv L L.rootRotation_action_one
  have hbzero : L.PrefixWordAction L.generatorB [1, 1, 0] [1, 0, 1] := by
    have hswap : L.PrefixWordAction L.rightRotation [1, 0, 1] [1, 1, 0] :=
      L.prefixInsertion_action L.rootRotation_action_zero_one [1]
    exact PrefixWordAction.inv L hswap
  have hbone : L.PrefixWordAction L.generatorB [1, 0] [1, 0, 0] := by
    have hswap : L.PrefixWordAction L.rightRotation [1, 0, 0] [1, 0] := by
      have hzz : L.PrefixWordAction L.rootRotation [0, 0] [0] := by
        unfold rootRotation
        rw [mul_assoc]
        refine PrefixWordAction.mul L (b := [1, 0]) ?_ ?_
        · exact L.cylinderSwap_action_right [0] [1, 0] (by decide) (by decide)
        · refine PrefixWordAction.mul L (b := [1, 0]) ?_ ?_
          · exact L.cylinderSwap_action_fixed [0] [1, 1] [1, 0] (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact PrefixWordAction.append L
              (L.cylinderSwap_action_left [0] [1] (by decide) (by decide)) [0]
      exact L.prefixInsertion_action hzz [1]
    exact PrefixWordAction.inv L hswap
  have hab : L.PrefixWordAction (L.generatorA * L.generatorB) [1, 1, 0] [0, 1, 1] :=
    PrefixWordAction.mul L (PrefixWordAction.append L hazero [1]) hbzero
  have hba : L.PrefixWordAction (L.generatorB * L.generatorA) [1, 1, 0] [1, 0, 0] :=
    PrefixWordAction.mul L hbone (PrefixWordAction.append L haone [0])
  intro hcommute
  have hwords : L.wordS [0, 1, 1] = L.wordS [1, 0, 0] := by
    calc
      L.wordS [0, 1, 1] =
          (↑(L.generatorA * L.generatorB) : A) * L.wordS [1, 1, 0] :=
        hab.prefixing.symm
      _ = (↑(L.generatorB * L.generatorA) : A) * L.wordS [1, 1, 0] := by
        rw [hcommute.eq]
      _ = L.wordS [1, 0, 0] := hba.prefixing
  apply (one_ne_zero : (1 : A) ≠ 0)
  calc
    (1 : A) = L.wordT [0, 1, 1] * L.wordS [0, 1, 1] :=
      (L.wordT_mul_wordS_self [0, 1, 1]).symm
    _ = L.wordT [0, 1, 1] * L.wordS [1, 0, 0] := by rw [hwords]
    _ = 0 :=
      L.wordT_mul_wordS_of_incomparable [0, 1, 1] [1, 0, 0] (by decide) (by decide)

/-- **The corner copy is not LEF**, unconditionally, for every ring carrying a
binary Leavitt family.  This discharges the manuscript's Proposition
`prop:vnotlef` without Higman's theorem. -/
theorem not_isLEF_cornerSubgroup_of_witness [Nontrivial A] :
    ¬ IsLEF L.cornerSubgroup :=
  L.not_isLEF_cornerSubgroup L.generatorA L.generatorB L.relator_one
    L.relator_two L.generators_not_commute

end LeavittFamily
end NonsoficGroupsExist
