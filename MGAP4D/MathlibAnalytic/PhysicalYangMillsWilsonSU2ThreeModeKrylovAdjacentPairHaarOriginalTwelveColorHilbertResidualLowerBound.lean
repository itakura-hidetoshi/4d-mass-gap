import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllLinkHaarMassFloorHilbertDefects
import Mathlib.Tactic

/-!
# P4-Q2-DP: original Wilson 12-color reference bounds actual Hilbert defects

DG proved that one genuine finite-volume strictly positive original
Perron-vacuum link-mass floor controls ALL original Wilson right/left
Haar reference integrals in the exact twelve-color average, retaining
the original 1/12 and each true physical color cardinality.

DO proved that every one of those literal Haar-mass-floor integrals
is exactly the same positive finite-volume scalar coefficient times
the right/left original physical pair-Haar CR conditional-expectation
Hilbert L² defect for each actual original physical link.

This file substitutes those EXACT right and left Hilbert identities in
EVERY genuine 12-color summand, with NO change of measure or weights,
and proves the resulting original Wilson twelve-color reference lower
bound for every bounded strongly measurable genuine joint observable.
All link defects live in the SAME original independent pair-Haar L².

The positive coefficient depends on H,N,beta. The next separate
obligation is to compare this physically normalized color average
with a positive finite-volume multiple of DC's UNNORMALIZED sum over
every actual left/right link and use DF to compare physical Wilson
variance. This is NOT a volume-uniform/continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Colors" => PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- The literal six-right/six-left original physical color average,
but now every Haar link variance is the TRUE unswapped original
pair-Haar Hilbert-L² coordinate projection defect from DO. -/
noncomputable def p4Q2DP_originalTwelveColorPairHaarHilbertFloorAverage
    (m : ℝ) (c : Colors) (f : JH) : ENNReal :=
  match c with
  | Sum.inl k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        ∑ e : p4Q2BA_ColorLinks H k,
          ENNReal.ofReal m *
            (ENNReal.ofReal (Real.exp (-32 * beta)) *
              ENNReal.ofReal (‖f - P (Sum.inr e.1) f‖ ^ 2))
  | Sum.inr k =>
      (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
        ∑ e : p4Q2BA_ColorLinks H k,
          ENNReal.ofReal m *
            (ENNReal.ofReal (Real.exp (-32 * beta)) *
              ENNReal.ofReal (‖f - P (Sum.inl e.1) f‖ ^ 2))

/-- The EXACT original normalization 1/12 of all twelve actual
left/right spatial color averages, with each true color cardinality. -/
noncomputable def p4Q2DP_originalTwelveColorPairHaarHilbertFloor
    (m : ℝ) (f : JH) : ENNReal :=
  (12 : ENNReal)⁻¹ *
    ∑ c : Colors,
      p4Q2DP_originalTwelveColorPairHaarHilbertFloorAverage
        H N beta m c f

/-- DG's original positive mass-floor energy is EXACTLY the true
12-color Haar Hilbert projection defect average. Unlike a new abstract
finite energy, this is an identity of the actual original reference
normalization on bounded physical representatives. -/
theorem p4Q2DP_originalTwelveColorHaarMassFloor_eq_L2_defects
    (m : ℝ) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    p4Q2DG_originalTwelveColorHaarMassFloor H N beta m F =
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor
        H N beta m f := by
  unfold p4Q2DG_originalTwelveColorHaarMassFloor
    p4Q2DP_originalTwelveColorPairHaarHilbertFloor
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  cases c with
  | inl k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            p4Q2DG_rightHaarMassFloor H N beta m e.1 F) =
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            ENNReal.ofReal m *
              (ENNReal.ofReal (Real.exp (-32 * beta)) *
                ENNReal.ofReal (‖f - P (Sum.inr e.1) f‖ ^ 2)))
      congr 1
      exact Finset.sum_congr rfl (fun e _he =>
        p4Q2DO_originalRightHaarMassFloor_eq_CR_defect
          H N hN beta hbeta m e.1 f F hF M hM hEq)
  | inr k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            p4Q2DG_leftHaarMassFloor H N beta m e.1 F) =
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H k,
            ENNReal.ofReal m *
              (ENNReal.ofReal (Real.exp (-32 * beta)) *
                ENNReal.ofReal (‖f - P (Sum.inl e.1) f‖ ^ 2)))
      congr 1
      exact Finset.sum_congr rfl (fun e _he =>
        p4Q2DO_originalLeftHaarMassFloor_eq_CR_defect
          H N hN beta hbeta m e.1 f F hF M hM hEq)

/-- Original mass-weighted physical Wilson twelve-color Haar reference
dominates a POSITIVE finite-volume normalized sum of ACTUAL CR pair-Haar
coordinate residuals over ALL genuine right/left spatial links. -/
theorem p4Q2DP_originalWilsonTwelveReference_ge_pairHaarHilbertFloor
    (f : JH) (F : Joint → ℝ)
    (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    ∃ m : ℝ, 0 < m ∧
      p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
  obtain ⟨m, hm, hOriginal⟩ :=
    p4Q2DG_originalTwelveColorHaarReference_ge_allLinkMassFloor
      H N hN beta hbeta
  refine ⟨m, hm, ?_⟩
  calc
    p4Q2DP_originalTwelveColorPairHaarHilbertFloor H N beta m f =
        p4Q2DG_originalTwelveColorHaarMassFloor H N beta m F :=
      (p4Q2DP_originalTwelveColorHaarMassFloor_eq_L2_defects
        H N hN beta hbeta m f F hF M hM hEq).symm
    _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := hOriginal F hF

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
