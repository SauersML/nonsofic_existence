import NonsoficGroupsExist.Leavitt.UniversalLeavittOver
import Mathlib.Algebra.Field.ZMod

/-!
# The universal binary Leavitt algebra over `ZMod 2`

This module gives short names for the `𝔽₂` specialization of the
field-parameterized construction in `UniversalLeavittOver`.
-/

namespace NonsoficGroupsExist
namespace UniversalLeavitt

abbrev Generator := BinaryLeavitt.Generator
abbrev Free := BinaryLeavitt.Free (ZMod 2)
abbrev Relation := BinaryLeavitt.Relation (ZMod 2)
abbrev BinaryLeavittAlgebra := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

def quotientMap : Free →ₐ[ZMod 2] BinaryLeavittAlgebra :=
  BinaryLeavitt.quotientMap (ZMod 2)

def generator (g : Generator) : BinaryLeavittAlgebra :=
  BinaryLeavitt.generator (ZMod 2) g

def family : LeavittFamily BinaryLeavittAlgebra :=
  BinaryLeavitt.family (ZMod 2)

noncomputable def lift {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (L : LeavittFamily A) : BinaryLeavittAlgebra →ₐ[ZMod 2] A :=
  BinaryLeavitt.lift L

end UniversalLeavitt
end NonsoficGroupsExist
