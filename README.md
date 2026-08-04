# NonsoficGroupsExist

This repository is a partial Lean formalization of a proposed construction of
a finitely presented nonsofic group. It does **not** currently prove that such
a group exists.

What is kernel-checked includes finite Hamming/sofic bookkeeping, localization,
finite-table covers, a represented algebra satisfying the binary Leavitt
relations, elementary-matrix embeddings and compression maps, and a genuine
two-generator non-LEF subgroup built from cylinder transpositions.  That
subgroup is embedded injectively into the concrete `EL₃` core by explicit
commutator and Whitehead identities.  The rank-four compressor words satisfy
the required conjugacy identities, generate the ambient `EL₄` together with
the core, and have the required centralization and trivial-intersection
properties.  `ConcreteRankFour.compressionSetup` assembles these facts into a
closed concrete algebraic setup.

The analytic development also constructs the GNS Hilbert space of every
limiting sofic correlation, proves the iterated Kazhdan contraction there,
uniformizes it back to all sufficiently large finite models, and controls the
approximate-multiplication error between exact group words and the actual
finite permutation Markov operator.  Consequently, genuine finite-model
Markov displacements satisfy an arbitrarily strong contraction, uniformly over
every centered indicator, with arbitrarily small normalized additive error.  The
one-step displacement is now related to the genuine directed generator-cut
energy, and centering has been eliminated from the threshold-rounding input.
Finite coarea rounding, maximal-bad-set removal, and finite support propagation
are also kernel-checked.  A geometric-series movement estimate now keeps the
replacement-set proximity coefficient independent of the Markov horizon; a
second maximal-bad-set argument removes its additive finite-model error.  The
resulting rounding theorem therefore has a fixed admissible input-cut
threshold even as the requested boundary ratio tends to zero.  Kun's complete
terminating finite partition recursion constructs blocks with a uniform global
cut inequality and a linear small-boundary budget.  The development charges
all inter-block generator edges to exceptional incidence or reference cuts and
constructs an explicit edit witness deleting them.  It does not yet perform
Kun's subsequent matching repair that turns the additive block inequalities
into genuine componentwise expansion.

The decisive remaining mathematics is not hidden behind theorem-shaped
parameters. In particular, the repository currently lacks proofs of the
required expander decomposition and Kun--Thom implication, the relevant
property `(T)` results.  The represented stream-operator algebra is not
identified with the universal Leavitt algebra, and the non-LEF witness is not
identified with Thompson's group `V`; neither identification is used by the
concrete compression setup.

`TableCover` proves a conditional reduction: a finitely generated nonsofic
group has a finitely presented nonsofic cover. It does not provide the initial
nonsofic group.
