import NonsoficGroupsExist.Covers.TableCover

/-!
# The sequential and the local definition of soficity agree

Definition `def:sofic` of the manuscript is sequential: a group is sofic when
there is a *sequence* of finite permutation models whose sizes diverge and whose
multiplicativity and faithfulness errors vanish in the limit.  The endpoint
statements of this development instead consume `IsSofic`, the local property
that every finite subset admits a model of every prescribed accuracy.

This module records that the two agree.  The sequential-to-local direction is
`isSofic_of_soficApproximation` (proved in `Sofic.Sofic`, with no countability
premise); the local-to-sequential direction is `soficApproximation_of_isSofic`
(proved in `Covers.TableCover`, where countability is used to exhaust the group
by an increasing sequence of finite subsets).  Both are needed for the iff, so
it lives here rather than in either source module.
-/

namespace NonsoficGroupsExist

/-- **Definitional correspondence with Definition `def:sofic`.**  For a
countable group the sequential object of the manuscript and the local predicate
used by the endpoint theorems define the same class of groups.

Countability is required only for the forward implication, which has to
assemble one sequence of models out of the local property; the backward
implication is `isSofic_of_soficApproximation` and holds for every group. -/
theorem isSofic_iff_nonempty_soficApproximation (G : Type*) [Group G]
    [Countable G] : IsSofic G ↔ Nonempty (SoficApproximation G) := by
  constructor
  · intro h
    exact soficApproximation_of_isSofic h
  · rintro ⟨A⟩
    exact isSofic_of_soficApproximation A

end NonsoficGroupsExist
