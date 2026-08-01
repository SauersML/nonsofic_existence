import NonsoficGroupsExist.Criterion
import NonsoficGroupsExist.Kazhdan
import Mathlib.GroupTheory.Finiteness

/-!
# Cited external inputs

The cited results are propositions supplied to the final assembly theorem, not
new constants.  Consequently a proof depending on one of these interfaces
records that proposition in its ordinary hypotheses; it never acquires a
user-defined kernel axiom.
-/

namespace NonsoficGroupsExist

/-- Kun's expander-decomposition theorem in exactly the form consumed by the
local criterion. -/
def KunTheorem : Prop :=
  ∀ (G : Type) [Group G] [Countable G] [Group.FG G],
    HasKazhdanPropertyT G → Infinite G →
      ∀ (S : SoficApproximation G) (T : Finset G),
        (∀ g ∈ T, g⁻¹ ∈ T) → Subgroup.closure (T : Set G) = ⊤ →
          Nonempty (ExpanderDecomposition S T)

/-- Kun--Thom's centralizer theorem in its essential-expander form. -/
def KunThomTheorem : Prop :=
  ∀ (K J : Type) [Group K] [Group J],
    KunThomHypothesis K J

end NonsoficGroupsExist
