import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic

/-!
# Local embeddability into finite groups

This file fixes the LEF vocabulary of Section `subsec:lef` and proves the one
technical fact needed to use it: a local embedding, being multiplicative on a
large enough finite set, evaluates fixed words correctly.  This is the
mechanism by which a relator of a finitely presented group is transported into
a finite group.
-/

namespace NonsoficGroupsExist

open scoped Pointwise

/-- A map that is multiplicative on a finite set and normalized at `1`. -/
structure LocalMultiplicativeOn {G H : Type*} [Group G] [Group H]
    (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y

namespace LocalMultiplicativeOn

variable {G H : Type*} [Group G] [Group H]

theorem mono {s t : Finset G} {f : G → H} (h : LocalMultiplicativeOn t f)
    (hst : s ⊆ t) : LocalMultiplicativeOn s f where
  map_one := h.map_one
  map_mul x hx y hy := h.map_mul x (hst hx) y (hst hy)

theorem map_inv_of_mem {s : Finset G} {f : G → H} (h : LocalMultiplicativeOn s f)
    {x : G} (hx : x ∈ s) (hi : x⁻¹ ∈ s) : f x⁻¹ = (f x)⁻¹ := by
  have hm := h.map_mul x hx x⁻¹ hi
  rw [mul_inv_cancel, h.map_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

end LocalMultiplicativeOn

/-- Section `subsec:lef`: `J` is locally embeddable into finite groups. -/
def IsLEF (J : Type*) [Group J] : Prop :=
  ∀ s : Finset J, ∃ (n : ℕ) (f : J → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set J) ∧ LocalMultiplicativeOn s f

/-- A finite group packaged as a target for textbook LEF models. -/
structure FiniteGroupModel where
  carrier : Type
  group : Group carrier
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteGroupModelCoeSort : CoeSort FiniteGroupModel Type :=
  ⟨FiniteGroupModel.carrier⟩
instance finiteGroupModelGroup (H : FiniteGroupModel) : Group H := H.group
instance finiteGroupModelFintype (H : FiniteGroupModel) : Fintype H := H.fintype
instance finiteGroupModelDecidableEq (H : FiniteGroupModel) : DecidableEq H :=
  H.decidableEq

/-- Textbook LEF: a partial embedding into an arbitrary finite group, with
multiplicativity required only when the tested product remains in the set. -/
def IsTextbookLEF (J : Type*) [Group J] : Prop :=
  ∀ s : Finset J, ∃ (H : FiniteGroupModel) (f : J → H),
    Set.InjOn f (s : Set J) ∧
      ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s → f (x * y) = f x * f y

/-- The permutation-target, globally defined convention used by this project
is equivalent to textbook LEF.  In the reverse direction we enlarge the test
set by `1` and all pairwise products, then apply the Cayley embedding. -/
theorem isLEF_iff_textbook (J : Type*) [Group J] :
    IsLEF J ↔ IsTextbookLEF J := by
  classical
  constructor
  · intro h s
    obtain ⟨n, f, hf, hmul⟩ := h s
    let H : FiniteGroupModel :=
      { carrier := Equiv.Perm (Fin n)
        group := inferInstance
        fintype := inferInstance
        decidableEq := inferInstance }
    exact ⟨H, f, hf, fun x hx y hy _ ↦ hmul.map_mul x hx y hy⟩
  · intro h s
    let T : Finset J := insert 1 (s ∪ s * s)
    obtain ⟨H, f, hf, hmul⟩ := h T
    let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
    let regular : H → Equiv.Perm (Fin (Fintype.card H)) := fun a ↦
      e.permCongr (Equiv.mulLeft a)
    have regular_injective : Function.Injective regular := by
      intro a b hab
      have hp := Equiv.Perm.congr_fun hab (e 1)
      apply e.injective
      simpa [regular, Equiv.permCongr_apply] using hp
    have honeT : (1 : J) ∈ T := by simp [T]
    have hf_one : f 1 = 1 := by
      have hm := hmul 1 honeT 1 honeT (by simp [T])
      have hm' : f 1 * 1 = f 1 * f 1 := by simpa using hm
      exact (mul_left_cancel hm').symm
    refine ⟨Fintype.card H, fun x ↦ regular (f x), ?_, ?_⟩
    · intro x hx y hy hxy
      apply hf (by simp [T, hx]) (by simp [T, hy])
      exact regular_injective hxy
    · constructor
      · ext z
        simp [regular, hf_one, Equiv.permCongr_apply]
      · intro x hx y hy
        have hm : f (x * y) = f x * f y :=
          hmul x (by simp [T, hx]) y (by simp [T, hy])
            (by
              simp only [T, Finset.mem_insert, Finset.mem_union]
              exact Or.inr (Or.inr (Finset.mul_mem_mul hx hy)))
        ext z
        simp [regular, Equiv.permCongr_apply, Equiv.Perm.mul_apply, hm]

/-- Every finite group is LEF, via its left regular action transported to a
standard finite type. -/
theorem isLEF_of_finite (G : Type) [Group G] [Finite G] : IsLEF G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  intro s
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let f : G → Equiv.Perm (Fin (Fintype.card G)) := fun g ↦
    e.permCongr (Equiv.mulLeft g)
  refine ⟨Fintype.card G, f, ?_, ?_⟩
  · intro x _ y _ hxy
    have h := Equiv.Perm.congr_fun hxy (e 1)
    have h' : e x = e y := by
      simpa [f, Equiv.permCongr_apply] using h
    exact e.injective h'
  · constructor
    · ext z
      simp [f, Equiv.permCongr_apply]
    · intro x _ y _
      ext z
      simp [f, Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- The infinite cyclic group is LEF, witnessed on each finite test set by an
exact cyclic quotient whose modulus separates that set. -/
theorem isLEF_multiplicative_int : IsLEF (Multiplicative ℤ) := by
  classical
  intro s
  let M : ℕ := s.sup fun g ↦ g.toAdd.natAbs
  let N : ℕ := 2 * M + 1
  have hN : N ≠ 0 := by simp [N]
  letI : NeZero N := ⟨hN⟩
  let φ : Multiplicative ℤ →* Multiplicative (ZMod N) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))
  let H := Multiplicative (ZMod N)
  letI : Fintype H := inferInstance
  letI : DecidableEq H := inferInstance
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let f : Multiplicative ℤ → Equiv.Perm (Fin (Fintype.card H)) := fun g ↦
    e.permCongr (Equiv.mulLeft (φ g))
  refine ⟨Fintype.card H, f, ?_, ?_⟩
  · intro g hg h hh hfh
    by_contra hgh
    have hp := Equiv.Perm.congr_fun hfh (e 1)
    have hφ : φ g = φ h := by
      apply e.injective
      simpa [f, Equiv.permCongr_apply] using hp
    have hcast : (g.toAdd : ZMod N) = (h.toAdd : ZMod N) := by
      simpa [φ] using congrArg Multiplicative.toAdd hφ
    have hdvd : (N : ℤ) ∣ h.toAdd - g.toAdd :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub g.toAdd h.toAdd N).mp hcast
    have hdiff : h.toAdd - g.toAdd ≠ 0 := by
      intro hz
      apply hgh
      have heq : h.toAdd = g.toAdd := sub_eq_zero.mp hz
      exact congrArg Multiplicative.ofAdd heq.symm
    have hlower : N ≤ (h.toAdd - g.toAdd).natAbs := by
      simpa only [Int.natAbs_natCast] using
        Int.natAbs_le_of_dvd_ne_zero hdvd hdiff
    have hgM : g.toAdd.natAbs ≤ M := by
      exact Finset.le_sup hg
    have hhM : h.toAdd.natAbs ≤ M := by
      exact Finset.le_sup hh
    have hupper := Int.natAbs_sub_le h.toAdd g.toAdd
    omega
  · constructor
    · ext z
      simp [f, φ, Equiv.permCongr_apply]
    · intro g _ h _
      ext z
      simp [f, Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- Every fixed element of a free group has a finite control set outside of
which local multiplicativity already forces the value of the corresponding
word.  This is the free-group form of Lemma `lem:word`, used to transport
relators into local embeddings. -/
theorem exists_local_word_control {α : Type*} {G : Type*} [Group G]
    (φ : FreeGroup α →* G) (z : FreeGroup α) :
    ∃ s : Finset G, ∀ (H : Type) [Group H] (f : G → H),
      LocalMultiplicativeOn s f →
        FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) z = f (φ z) := by
  classical
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · refine ⟨∅, ?_⟩
    intro H _ f hf
    simp [hf.map_one]
  · intro a
    refine ⟨∅, ?_⟩
    intro H _ f _
    simp
  · intro a _
    refine ⟨{φ (FreeGroup.of a), (φ (FreeGroup.of a))⁻¹}, ?_⟩
    intro H _ f hf
    simp only [map_inv, FreeGroup.lift_apply_of]
    exact (hf.map_inv_of_mem (by simp) (by simp)).symm
  · intro x y hx hy
    obtain ⟨sx, hx⟩ := hx
    obtain ⟨sy, hy⟩ := hy
    refine ⟨insert (φ x) (insert (φ y) (sx ∪ sy)), ?_⟩
    intro H _ f hf
    have hsx : sx ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    have hsy : sy ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    calc
      FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) (x * y) =
          FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) x *
            FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) y := map_mul _ _ _
      _ = f (φ x) * f (φ y) :=
        congrArg₂ (· * ·) (hx H f (hf.mono hsx)) (hy H f (hf.mono hsy))
      _ = f (φ x * φ y) := (hf.map_mul (φ x) (by simp) (φ y) (by simp)).symm
      _ = f (φ (x * y)) := by rw [map_mul]

end NonsoficGroupsExist
