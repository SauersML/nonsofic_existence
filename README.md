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
