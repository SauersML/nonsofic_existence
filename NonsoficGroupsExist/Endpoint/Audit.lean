import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Sofic.FinitelyPresentedLEF
import NonsoficGroupsExist.Leavitt.UnitsGLProfile
import NonsoficGroupsExist.KOne.AllRanksElementary
import NonsoficGroupsExist.Sofic.SoficPositiveControl
import NonsoficGroupsExist.Kun.KunDecomposition
import NonsoficGroupsExist.KunThom.KunThomTheorem
import NonsoficGroupsExist.PropertyT.FreeElementaryPropertyT
import NonsoficGroupsExist.Kazhdan.KazhdanComplex
import NonsoficGroupsExist.Kazhdan.KazhdanUniverse
import NonsoficGroupsExist.KOne.RefineLoopDischarge
import NonsoficGroupsExist.Kazhdan.ShalomFinitePresentation
import NonsoficGroupsExist.Covers.KazhdanCover

/-!
# Human-readable axiom report

This module pins the axiom reports for the public results and the three most
load-bearing mathematical inputs.  It is imported by the library root, so a
normal `lake build` prints these reports.  The stricter executable gate in
`scripts/Audit.lean` independently traverses the transitive axiom closure of
the entire project namespace and fails on anything beyond classical Lean.
-/

#print axioms NonsoficGroupsExist.nonsofic_groups_exist
#print axioms NonsoficGroupsExist.universalLeavittEL4_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittEL3_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittUnits_not_isSofic
#print axioms NonsoficGroupsExist.universalLeavittGL_not_isSofic
#print axioms NonsoficGroupsExist.ambient_profile
#print axioms NonsoficGroupsExist.ambient_full_profile
#print axioms NonsoficGroupsExist.universalLeavitt_profile
#print axioms NonsoficGroupsExist.binaryLeavitt_finiteField_profile
#print axioms NonsoficGroupsExist.exists_finitelyPresented_nonsofic_group
#print axioms NonsoficGroupsExist.exists_infinite_finitelyPresented_nonsofic_ambient_cover
#print axioms NonsoficGroupsExist.KunDecomposition.exists_expanderDecomposition
#print axioms NonsoficGroupsExist.KunSelectiveRepairExpansion.refined_bad_component_expands_at_every_positive_constant
#print axioms NonsoficGroupsExist.KunThomTheorem.isLEF_of_exactProductExpansion
#print axioms NonsoficGroupsExist.FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT
#print axioms NonsoficGroupsExist.UniversalRankFour.witness_not_isLEF
#print axioms NonsoficGroupsExist.ThompsonFObstruction.finite_image_generatorCommutator_eq_one
#print axioms NonsoficGroupsExist.isSofic_of_finite
#print axioms NonsoficGroupsExist.isSofic_multiplicative_int
#print axioms NonsoficGroupsExist.isSofic_iff_productRestricted
#print axioms NonsoficGroupsExist.isLEF_of_finite
#print axioms NonsoficGroupsExist.isLEF_multiplicative_int
#print axioms NonsoficGroupsExist.isLEF_iff_textbook
#print axioms NonsoficGroupsExist.isKazhdanPair_iff_complex
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_iff_complex
#print axioms NonsoficGroupsExist.IsKazhdanPair.liftUniverse
#print axioms NonsoficGroupsExist.HasKazhdanPropertyT.liftUniverse
#print axioms NonsoficGroupsExist.IsKazhdanPair.lowerUniverse
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_universe_iff
#print axioms NonsoficGroupsExist.hasKazhdanPropertyT_iff_textbook

-- The unconditional K₁-vanishing chain (session 54): narrow reduction,
-- scalar reduction, checkpoint B4, GL = EL, and the Whitehead-form
-- headline.  All must report only the three standard axioms.
#print axioms NonsoficGroupsExist.BinaryLeavitt.narrowReduction_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.scalarReduction_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.stableUnits_eq_top_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.glTwo_eq_elementary_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.glFour_eq_elementary_holds
#print axioms NonsoficGroupsExist.BinaryLeavitt.K1_trivial

-- The unit-group and general-linear profiles (Theorem B(i) closed): finite
-- generation, infinitude, property (T), and nonsoficity of `L_k(1,2)ˣ` and
-- of every positive-rank `GL_r` over every finite field.
#print axioms NonsoficGroupsExist.binaryLeavittUnits_profile
#print axioms NonsoficGroupsExist.binaryLeavittGL_profile

-- Theorem C's Kazhdan half.  These were proved but sat outside this module's
-- import closure, so an ordinary build never reported their axioms and the
-- manuscript's alignment table lost track of them entirely -- it recorded
-- `thm:kcover` as manuscript-only while the theorem was sitting here, proved.
-- Shalom's theorem is proved internally rather than cited, so it belongs in
-- the report alongside the Kun and Kun--Thom inputs it sits next to in the
-- paper's trust surface.
#print axioms NonsoficGroupsExist.Shalom.exists_presented_kazhdan_cover
#print axioms NonsoficGroupsExist.Shalom.exists_finitelyPresented_kazhdan_cover
#print axioms NonsoficGroupsExist.exists_kazhdan_finitelyPresented_cover_of_not_isSofic

-- All-ranks collapse, perfectness, and the rank-two compression over
-- `L_k(1,2)`: `GL_n = EL_n` for every `n ≥ 2` over every field, the unit
-- group is perfect, and the two-by-two Leavitt-corner theorem closes over
-- every finite field.
#print axioms NonsoficGroupsExist.BinaryLeavitt.elementaryGroup_eq_top
#print axioms NonsoficGroupsExist.BinaryLeavitt.glAll_eq_elementary
#print axioms NonsoficGroupsExist.BinaryLeavitt.binaryLeavittUnits_perfect
#print axioms NonsoficGroupsExist.binaryLeavittRankTwo_not_isSofic

-- `lem:fplef`, closed: finitely presented LEF groups are residually finite.
#print axioms NonsoficGroupsExist.finitelyPresented_isLEF_residuallyFinite
