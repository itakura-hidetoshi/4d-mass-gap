import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonVarianceTwelveColorCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalBoundedCoreKernelExactFrontier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletOperatorGap
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-DV: GENUINE original Wilson Haar Riesz quadratic lower coercivity

DQ bounds the original NORMALIZED 12-color Wilson mass-weighted Haar reference
from below by actual full pair-Haar Hilbert coordinate defects, while DC and
DF bound genuine original Wilson variance through the independent pair-Haar
variance. DR previously combined the chain only with the separate physical
D12 residual. Here we retain the exact intermediate ORIGINAL WILSON HAAR
REFERENCE lower bound rather than replacing it by D12.

The actual original Wilson reference quadratic Qcore is the real value of
the UNNORMALIZED sum of 12 actual color averages; the normalized Haar
reference is 1/12 times this sum. We use only the rigorously verified
nonnegative direction normalized ≤ unnormalized (no hidden factor).
The finite physical Wilson L² quotient BR/CL and dense BW core then extend
the same strictly positive finite-volume coefficient to the FULL original
physical Wilson joint L² continuous Riesz quadratic BX, NOT the D12 form.

This will close the prior CL full-L² zero-kernel obstruction by a genuine
continuous coercive inequality, not by a false claim that the intersection
of a dense subspace with a closed kernel is dense.

No volume-uniform, spacing-scaled or 4D continuum Yang-Mills mass gap is
claimed. Coefficient depends on H,N,beta, and no new axiom is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2600000
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
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muWilson" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta

local instance p4Q2DV_constantLineHasOrthogonalProjection :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change W.HasOrthogonalProjection
  letI : FiniteDimensional ℝ W := by
    unfold W
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace W

/-- The exact intermediate quantitative original Haar reference bound
previously internal to DR: a single positive finite-volume coefficient
controls genuine original Wilson variance on the physical bounded core. -/
theorem p4Q2DV_originalWilsonNormalizedHaarReference_ge_wilsonVariance_bounded :
    ∃ κ : ENNReal, 0 < κ ∧
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F),
        ∀ (B : ℝ) (hB : ∀ z, ‖F z‖ ≤ B)
          (f : JH), F =ᵐ[muPair] (f : Joint → ℝ) →
            κ * ENNReal.ofReal (variance F muWilson) ≤
              p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2DQ_originalWilsonTwelveReference_ge_allCoordinateHilbertDefects
      H N hN beta hbeta
  obtain ⟨mW, M, hmW, hM, hVariance⟩ :=
    p4Q2DF_originalWilsonJoint_allBoundedVariance_uniform_sandwich
      H N hN beta hbeta
  let a : ENNReal := p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
  let b : ENNReal := ENNReal.ofReal (M + 1)
  let κ : ENNReal := a * b⁻¹
  have ha : 0 < a :=
    p4Q2DQ_allLinkHilbertFloorCoefficient_pos H beta m hm
  have hplus : 0 < M + 1 := by linarith
  have hb0 : b ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hplus)
  have hbTop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hκ : 0 < κ :=
    (ENNReal.mul_pos_iff).2 ⟨ha, ENNReal.inv_pos.mpr hbTop⟩
  refine ⟨κ, hκ, ?_⟩
  intro F hF B hB f hEq
  have hVarianceUpper : variance F muWilson ≤ M * variance F muPair :=
    (hVariance F hF B hB).2
  have hPairNonneg : 0 ≤ variance F muPair :=
    variance_nonneg F muPair
  have hVariancePlus :
      variance F muWilson ≤ (M + 1) * variance F muPair := by
    calc
      variance F muWilson ≤ M * variance F muPair := hVarianceUpper
      _ ≤ M * variance F muPair + variance F muPair :=
        le_add_of_nonneg_right hPairNonneg
      _ = (M + 1) * variance F muPair := by ring
  have hVarianceENN :
      ENNReal.ofReal (variance F muWilson) ≤
        b * ENNReal.ofReal (variance F muPair) := by
    change ENNReal.ofReal (variance F muWilson) ≤
      ENNReal.ofReal (M + 1) * ENNReal.ofReal (variance F muPair)
    calc
      ENNReal.ofReal (variance F muWilson) ≤
        ENNReal.ofReal ((M + 1) * variance F muPair) :=
          ENNReal.ofReal_le_ofReal hVariancePlus
      _ = ENNReal.ofReal (M + 1) *
            ENNReal.ofReal (variance F muPair) :=
          ENNReal.ofReal_mul hplus.le
  have hPairDefects :
      ENNReal.ofReal (variance F muPair) ≤
        ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) := by
    calc
      ENNReal.ofReal (variance F muPair) =
        ENNReal.ofReal (variance (f : Joint → ℝ) muPair) :=
          congrArg ENNReal.ofReal (variance_congr hEq)
      _ ≤ ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) :=
          p4Q2DR_actualPairHaarVariance_le_allCoordinateENNRealDefects
            H N f
  have hPairReference :
      a * ENNReal.ofReal (variance F muPair) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
    calc
      a * ENNReal.ofReal (variance F muPair) ≤
        a * (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) := by
          calc
            a * ENNReal.ofReal (variance F muPair) =
              ENNReal.ofReal (variance F muPair) * a := mul_comm _ _
            _ ≤ (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) * a :=
              mul_le_mul_left hPairDefects a
            _ = a * (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) :=
              mul_comm _ _
      _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F :=
        hReference f F hF B hB hEq
  have hCancel :
      κ * (b * ENNReal.ofReal (variance F muPair)) =
        a * ENNReal.ofReal (variance F muPair) := by
    change (a * b⁻¹) * (b * ENNReal.ofReal (variance F muPair)) =
      a * ENNReal.ofReal (variance F muPair)
    calc
      (a * b⁻¹) * (b * ENNReal.ofReal (variance F muPair)) =
        a * ((b⁻¹ * b) * ENNReal.ofReal (variance F muPair)) := by ac_rfl
      _ = a * ENNReal.ofReal (variance F muPair) := by
        rw [ENNReal.inv_mul_cancel hb0 hbTop, one_mul]
  have hRefVariance :
      κ * ENNReal.ofReal (variance F muWilson) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
    calc
      κ * ENNReal.ofReal (variance F muWilson) ≤
        κ * (b * ENNReal.ofReal (variance F muPair)) := by
          calc
            κ * ENNReal.ofReal (variance F muWilson) =
              ENNReal.ofReal (variance F muWilson) * κ := mul_comm _ _
            _ ≤ (b * ENNReal.ofReal (variance F muPair)) * κ :=
              mul_le_mul_left hVarianceENN κ
            _ = κ * (b * ENNReal.ofReal (variance F muPair)) :=
              mul_comm _ _
      _ = a * ENNReal.ofReal (variance F muPair) := hCancel
      _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F := hPairReference
  exact hRefVariance

local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- Pass the normalized ORIGINAL Wilson Haar reference to its distinct
unnormalized real quadratic, using the EXACT 1/12 convention. The smaller
coefficient min κ 1 is strictly positive and finite even without assuming
an ENNReal coefficient is finite. -/
theorem p4Q2DV_originalWilsonReferenceReal_ge_wilsonVariance_bounded :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F)
        (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
          c * variance F muWilson ≤
            p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
              H N hN beta hbeta F := by
  obtain ⟨k, hk, hNormalized⟩ :=
    p4Q2DV_originalWilsonNormalizedHaarReference_ge_wilsonVariance_bounded
      H N hN beta hbeta
  let γ : ENNReal := min k 1
  have hγPos : 0 < γ := lt_min hk (by norm_num)
  have hγTop : γ ≠ ∞ := ne_of_lt
    (lt_of_le_of_lt (min_le_right k (1 : ENNReal)) (by norm_num))
  have hγReal : 0 < γ.toReal :=
    ENNReal.toReal_pos hγPos.ne' hγTop
  refine ⟨γ.toReal, hγReal, ?_⟩
  letI : IsProbabilityMeasure muPair := by infer_instance
  letI : IsProbabilityMeasure muWilson :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  intro F hF bound hbound
  have hPairMem : MemLp F 2 muPair :=
    MemLp.of_bound hF.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hbound)
  let f : JH := hPairMem.toLp F
  have hEq : F =ᵐ[muPair] (f : Joint → ℝ) :=
    (MemLp.coeFn_toLp hPairMem).symm
  have hNormalizedRef :=
    hNormalized F hF bound hbound f hEq
  have hVarNonneg : 0 ≤ variance F muWilson :=
    variance_nonneg F muWilson
  have hGammaRef :
      γ * ENNReal.ofReal (variance F muWilson) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
    calc
      γ * ENNReal.ofReal (variance F muWilson) =
        ENNReal.ofReal (variance F muWilson) * γ := mul_comm _ _
      _ ≤ ENNReal.ofReal (variance F muWilson) * k :=
        mul_le_mul_right (min_le_left k (1 : ENNReal)) _
      _ = k * ENNReal.ofReal (variance F muWilson) := mul_comm _ _
      _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F := hNormalizedRef
  let sumRef : ENNReal :=
    ∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c F
  have hSumTop : sumRef ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta F hF bound hbound
  have hInv : (12 : ENNReal)⁻¹ ≤ 1 := by norm_num
  have hAverage_le_sum :
      p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F ≤ sumRef := by
    change (12 : ENNReal)⁻¹ * sumRef ≤ sumRef
    calc
      (12 : ENNReal)⁻¹ * sumRef = sumRef * (12 : ENNReal)⁻¹ :=
        mul_comm _ _
      _ ≤ sumRef * 1 := mul_le_mul_right hInv sumRef
      _ = sumRef := mul_one _
  have hReal :=
    ENNReal.toReal_mono hSumTop (hGammaRef.trans hAverage_le_sum)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hVarNonneg] at hReal
  change γ.toReal * variance F muWilson ≤
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F at hReal
  exact hReal

/-- Crucial full-space result: the ACTUAL original Wilson Haar reference
continuous quadratic energy controls true Wilson-constant-orthogonal
squared norm on ALL original physical Wilson joint Hilbert L² classes. -/
theorem p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : J, κ * ‖x - B x‖ ^ 2 ≤ Q x := by
  obtain ⟨κ, hκ, hCoreRef⟩ :=
    p4Q2DV_originalWilsonReferenceReal_ge_wilsonVariance_bounded
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  have hclosed : IsClosed
      {x : J | κ * ‖x - B x‖ ^ 2 ≤ Q x} :=
    isClosed_le (by fun_prop)
      (p4Q2BX_originalFullJointQuadratic_continuous H N hN beta hbeta)
  intro x
  refine hd.induction_on x hclosed ?_
  intro y
  let F : Core :=
    p4Q2BV_originalCoreRepresentative H N hN beta hbeta y
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hRep : T F = (y : J) :=
    p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta y
  have hVarCong :
      variance ((T F : J) : Joint → ℝ) muWilson =
        variance F.1 muWilson :=
    variance_congr
      (p4Q2CL_originalBoundedCoreToPhysical_coeFn H N hN beta hbeta F)
  have hMinimal :
      ‖T F - B (T F)‖ ^ 2 ≤
        variance ((T F : J) : Joint → ℝ) muWilson :=
    p4Q2DS_centeredL2NormSq_le_wilsonVariance
      H N hN beta hbeta (T F)
  have hQcore : Q (T F) =
      p4Q2BP_originalCoreReference H N hN beta hbeta F :=
    p4Q2CL_originalFullQuadratic_eq_literalCore H N hN beta hbeta F
  have hCore :
      κ * ‖T F - B (T F)‖ ^ 2 ≤ Q (T F) := by
    calc
      κ * ‖T F - B (T F)‖ ^ 2 ≤
          κ * variance ((T F : J) : Joint → ℝ) muWilson :=
        mul_le_mul_of_nonneg_left hMinimal hκ.le
      _ = κ * variance F.1 muWilson := by rw [hVarCong]
      _ ≤ Q (T F) := by
        rw [hQcore]
        exact hCoreRef F.1 hF bound hbound
  change κ * ‖(y : J) - B (y : J)‖ ^ 2 ≤ Q (y : J)
  rw [← hRep]
  exact hCore

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
