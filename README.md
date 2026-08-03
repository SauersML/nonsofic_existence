# NonsoficGroupsExist

This repository is a partial Lean formalization of a proposed construction of
a finitely presented nonsofic group. It does **not** currently prove that such
a group exists.

What is kernel-checked includes finite Hamming/sofic bookkeeping, localization,
finite-table covers, a represented algebra satisfying the binary Leavitt
relations, elementary-matrix embeddings and compression maps, and a genuine
two-generator non-LEF subgroup of a Leavitt-family unit group.

The decisive remaining mathematics is not hidden behind theorem-shaped
parameters. In particular, the repository currently lacks proofs of the
required expander decomposition and Kun--Thom implication, the relevant
property `(T)` results, the ambient-generation theorem for the rank-four words,
and an embedding of the non-LEF witness into the elementary core. The
rank-four conjugacy identities themselves are kernel-checked. The represented stream-operator algebra is
also not identified with the universal Leavitt algebra, and the non-LEF witness
is not identified with Thompson's group `V`.

`TableCover` proves a conditional reduction: a finitely generated nonsofic
group has a finitely presented nonsofic cover. It does not provide the initial
nonsofic group.
