import NonsoficGroupsExist.LeavittCorner
import NonsoficGroupsExist.ThompsonFObstruction

/-!
# The compression scheme: the two corners

This file assembles Section `subsec:corner` of the manuscript at the level of
unit groups.  Over any ring carrying a binary Leavitt family:

* `compressedSubgroup` is the image `K` of the compression `a ↦ p₁ + s₀ a t₀`;
* `cornerSubgroup` is the image `J` of the complementary corner
  `a ↦ p₀ + s₁ a t₁`;
* `commute_compressed_corner` is `[K,J] = 1` (Proposition `prop:KJ`);
* `compressed_inf_corner` is `K ∩ J = 1` (Proposition `prop:KJ`).

Finally `not_isLEF_cornerSubgroup` supplies the manuscript's non-LEF input in
Higman-free form: a noncommuting pair of units satisfying the two standard
Thompson-`F` relations transports through the corner embedding, so the corner
copy is not LEF. This avoids any identification with a named Thompson group;
the proof uses the elementary argument of `ThompsonFObstruction`.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The compressed copy `K = q₀ Γ q₀⁻¹` of Section `subsec:corner`. -/
def compressedSubgroup : Subgroup Aˣ := L.compressedHom.range

/-- The commuting corner copy `J` of Section `subsec:corner`. -/
def cornerSubgroup : Subgroup Aˣ := L.cornerHom.range

theorem mem_compressedSubgroup (u : Aˣ) :
    L.compressedHom u ∈ L.compressedSubgroup := ⟨u, rfl⟩

theorem mem_cornerSubgroup (u : Aˣ) : L.cornerHom u ∈ L.cornerSubgroup :=
  ⟨u, rfl⟩

/-- **Proposition `prop:KJ`, first half**: the two corner images commute. -/
theorem commute_compressed_corner {x y : Aˣ} (hx : x ∈ L.compressedSubgroup)
    (hy : y ∈ L.cornerSubgroup) : Commute x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact L.compressedHom_commutes_cornerHom u v

/-- **Proposition `prop:KJ`, second half**: the two corner images intersect
trivially. -/
theorem compressed_inf_corner :
    L.compressedSubgroup ⊓ L.cornerSubgroup = ⊥ := by
  apply le_antisymm
  · rintro x ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    have huv : L.compressedHom u = L.cornerHom v := hv.symm
    obtain ⟨hu, -⟩ := (L.compressedHom_eq_cornerHom_iff u v).mp huv
    simp [hu]
  · exact bot_le

/-- The corner embedding, corestricted to its image. -/
def cornerHomRange : Aˣ →* L.cornerSubgroup :=
  L.cornerHom.codRestrict L.cornerSubgroup L.mem_cornerSubgroup

theorem cornerHomRange_injective : Function.Injective L.cornerHomRange := by
  intro u v huv
  apply L.cornerHom_injective
  exact congrArg Subtype.val huv

/-- **Higman-free replacement for Proposition `prop:vnotlef`.**  If the ambient
unit group contains two noncommuting units satisfying the two standard Thompson-`F`
relations, then the commuting corner copy is not LEF. -/
theorem not_isLEF_cornerSubgroup (a b : Aˣ)
    (h₁ : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (h₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2))
    (hne : ¬ Commute a b) : ¬ IsLEF L.cornerSubgroup := by
  set f : Aˣ →* L.cornerSubgroup := L.cornerHomRange with hf
  have hinj : Function.Injective f := L.cornerHomRange_injective
  have hf₁ : Commute (f a * (f b)⁻¹) ((f a)⁻¹ * f b * f a) := by
    simpa using h₁.map f
  have hf₂ : Commute (f a * (f b)⁻¹) (((f a) ^ 2)⁻¹ * f b * (f a) ^ 2) := by
    simpa using h₂.map f
  have hfne : ¬ Commute (f a) (f b) := by
    intro hcom
    apply hne
    apply (commute_iff_eq a b).2
    apply hinj
    simpa using hcom.eq
  exact ThompsonFObstruction.not_isLEF_of_two_relations (f a) (f b) hf₁ hf₂ hfne

/-- The compressed copy is likewise not LEF when the ambient unit group carries
the witness; this is the statement used when the roles of the two corners are
exchanged in the rank-two realization. -/
theorem not_isLEF_compressedSubgroup (a b : Aˣ)
    (h₁ : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (h₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2))
    (hne : ¬ Commute a b) : ¬ IsLEF L.compressedSubgroup := by
  set f : Aˣ →* L.compressedSubgroup :=
    L.compressedHom.codRestrict L.compressedSubgroup L.mem_compressedSubgroup
    with hf
  have hinj : Function.Injective f := by
    intro u v huv
    apply L.compressedHom_injective
    exact congrArg Subtype.val huv
  have hf₁ : Commute (f a * (f b)⁻¹) ((f a)⁻¹ * f b * f a) := by
    simpa using h₁.map f
  have hf₂ : Commute (f a * (f b)⁻¹) (((f a) ^ 2)⁻¹ * f b * (f a) ^ 2) := by
    simpa using h₂.map f
  have hfne : ¬ Commute (f a) (f b) := by
    intro hcom
    apply hne
    apply (commute_iff_eq a b).2
    apply hinj
    simpa using hcom.eq
  exact ThompsonFObstruction.not_isLEF_of_two_relations (f a) (f b) hf₁ hf₂ hfne

end LeavittFamily
end NonsoficGroupsExist
