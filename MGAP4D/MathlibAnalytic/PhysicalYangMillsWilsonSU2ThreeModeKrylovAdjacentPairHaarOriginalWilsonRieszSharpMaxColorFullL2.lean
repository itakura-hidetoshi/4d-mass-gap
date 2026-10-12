import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharpMaxColorWilsonHaarFloor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-EC: actual sharp maximum-color floor propagated through ORIGINAL Wilson Riesz

EB's Lean-proven true six-color maximum link cardinality improves DQ's
old 1/total-spatialLinkCard lower coefficient without changing the actual
Wilson Haar link-fiber mass m>0, its physical versus pair-Haar variance
upper comparison M>=0, or the exact original independent Haar Fubini
coordinates. DZ previously restored the exact factor 12 when moving the
genuine normalized original Haar reference to the actual UNNORMALIZED
original Wilson Haar Riesz sum.

Here both improvements are combined and propagated into the ACTUAL original
physical Wilson full-joint L² quadratic and its Riesz operator. Precisely

  a_EB(H,beta,m) = (12:ENNReal)^(-1) * (maxColorCard(H):ENNReal)^(-1)
                    * ofReal(m) * ofReal(exp(-32 beta));
  kappa_EC = 12 * (min (a_EB * ofReal(M+1)^(-1)) 1).toReal.

The SAME actual physical DQ/DF/DG witnesses are retained; no other Wilson
measure, artificial color weights, beta-zero replacement, or false identity
with the distinct normalized physical D12 is introduced. This finite-H
certificate still involves the size of an entire spatial color class and
the finite-volume original Wilson/Perron mass and density comparison.
It is NOT a volume/spacing-uniform physical spectral gap or continuum
Yang--Mills mass gap. Signed fine/frozen Gram and physical time remain open.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace NNReal

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

local instance p4Q2EC_constantLineHasOrthogonalProjection :
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

/-- The new normalized genuine max-color Wilson reference witness. -/
noncomputable def p4Q2EC_normalizedMaxColorCoefficient
    (m M : ℝ) : ℝ :=
  (min
    (p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
      (ENNReal.ofReal (M + 1))⁻¹)
    1).toReal

/-- Its physical DQ/DF witness inputs imply strict positivity at fixed
finite volume. It is NOT uniformly positive as H varies from this proof. -/
theorem p4Q2EC_normalizedMaxColorCoefficient_pos
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) :
    0 < p4Q2EC_normalizedMaxColorCoefficient H beta m M := by
  let a : ENNReal := p4Q2EB_maxColorHilbertFloorCoefficient H beta m
  let b : ENNReal := ENNReal.ofReal (M + 1)
  let k : ENNReal := a * b⁻¹
  have _hPhysicalUpperPos : 0 < M + 1 := by linarith
  have ha : 0 < a :=
    p4Q2EB_maxColorHilbertFloorCoefficient_pos H beta m hm
  have hbTop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hk : 0 < k :=
    (ENNReal.mul_pos_iff).2 ⟨ha, ENNReal.inv_pos.mpr hbTop⟩
  have hγ : 0 < min k 1 := lt_min hk (by norm_num)
  have hγTop : min k 1 ≠ ∞ := ne_of_lt
    (lt_of_le_of_lt (min_le_right k (1 : ENNReal)) (by norm_num))
  change 0 < (min k 1).toReal
  exact ENNReal.toReal_pos hγ.ne' hγTop

/-- Coefficient for the ORIGINAL unnormalized 12-color Wilson Haar Riesz
quadratic: combines EB's actual maximum-color cardinal with DZ's exact 12. -/
noncomputable def p4Q2EC_originalSharpMaxColorRieszCoefficient (m M : ℝ) : ℝ :=
  (12 : ℝ) * p4Q2EC_normalizedMaxColorCoefficient H beta m M

theorem p4Q2EC_originalSharpMaxColorRieszCoefficient_pos
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) :
    0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M := by
  unfold p4Q2EC_originalSharpMaxColorRieszCoefficient
  exact mul_pos (by norm_num)
    (p4Q2EC_normalizedMaxColorCoefficient_pos H beta m M hm hM)

/-- The SAME m,M witnesses yield an EC coefficient at least as large as
DZ's earlier genuine original-Wilson coefficient: not a new H-uniformity. -/
theorem p4Q2EC_DZCoefficient_le_originalSharpMaxColor
    (m M : ℝ) :
    p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M ≤
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M := by
  let a : ENNReal := p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
  let a' : ENNReal := p4Q2EB_maxColorHilbertFloorCoefficient H beta m
  let b : ENNReal := (ENNReal.ofReal (M + 1))⁻¹
  have hA : a ≤ a' := p4Q2EB_oldFloor_le_maxColorFloor H beta m
  have hProd : a * b ≤ a' * b := by
    simpa [mul_comm] using (mul_le_mul_right hA b)
  have hMin : min (a * b) 1 ≤ min (a' * b) (1 : ENNReal) :=
    min_le_min hProd le_rfl
  have hTop : min (a' * b) 1 ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  have hReal : (min (a * b) 1).toReal ≤ (min (a' * b) 1).toReal :=
    ENNReal.toReal_mono hTop hMin
  change (12 : ℝ) * (min (a * b) 1).toReal ≤
    (12 : ℝ) * (min (a' * b) 1).toReal
  exact mul_le_mul_of_nonneg_left hReal (by norm_num)

/-- Genuine original Wilson normalized Haar reference with true
six-color maximum cardinality and actual Wilson/Haar variance comparison. -/
theorem p4Q2EC_originalNormalizedReference_maxColorWitness :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ (F : Joint → ℝ) (_hF : StronglyMeasurable F),
        ∀ (bound : ℝ) (_hbound : ∀ z, ‖F z‖ ≤ bound)
          (f : JH), F =ᵐ[muPair] (f : Joint → ℝ) →
            (p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
                (ENNReal.ofReal (M + 1))⁻¹) *
                ENNReal.ofReal (variance F muWilson) ≤
              p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2EB_originalWilsonTwelveReference_ge_maxColorHilbertDefects
      H N hN beta hbeta
  obtain ⟨_mW, M, _hmW, hM, hVariance⟩ :=
    p4Q2DF_originalWilsonJoint_allBoundedVariance_uniform_sandwich
      H N hN beta hbeta
  let a : ENNReal := p4Q2EB_maxColorHilbertFloorCoefficient H beta m
  let b : ENNReal := ENNReal.ofReal (M + 1)
  let κ : ENNReal := a * b⁻¹
  -- DQ supplies the actual positive mass witness; no extra positivity assumption.
  have hplus : 0 < M + 1 := by linarith
  have hb0 : b ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hplus)
  have hbTop : b ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨m, M, hm, hM, ?_⟩
  intro F hF B hB f hEq
  change κ * ENNReal.ofReal (variance F muWilson) ≤
    p4Q2BC_originalPhysicalTwelveColorHaarReference H N hN beta hbeta F
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

/-- Exact UNNORMALIZED original Wilson reference with the sharper maximum
color cardinality and unchanged original physical mass and M witnesses. -/
theorem p4Q2EC_originalUnnormalizedReference_maxColorWitness :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      ∀ (F : Joint → ℝ) (_hF : StronglyMeasurable F)
        (bound : ℝ) (_hbound : ∀ z, ‖F z‖ ≤ bound),
        p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
            variance F muWilson ≤
          p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
            H N hN beta hbeta F := by
  obtain ⟨m, M, hm, hM, hNorm⟩ :=
    p4Q2EC_originalNormalizedReference_maxColorWitness
      H N hN beta hbeta
  let k : ENNReal :=
    p4Q2EB_maxColorHilbertFloorCoefficient H beta m *
      (ENNReal.ofReal (M + 1))⁻¹
  let γ : ENNReal := min k 1
  have hPos : 0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M :=
    p4Q2EC_originalSharpMaxColorRieszCoefficient_pos H beta m M hm hM
  refine ⟨m, M, hm, hM, hPos, ?_⟩
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
  have hNormBound := hNorm F hF bound hbound f hEq
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
            H N hN beta hbeta F := hNormBound
  let sumRef : ENNReal :=
    ∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c F
  have hSumFinite : sumRef ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta F hF bound hbound
  have hExact :
      (12 : ENNReal) * (γ * ENNReal.ofReal (variance F muWilson)) ≤
        sumRef := by
    calc
      (12 : ENNReal) * (γ * ENNReal.ofReal (variance F muWilson)) ≤
          (12 : ENNReal) *
            p4Q2BC_originalPhysicalTwelveColorHaarReference
              H N hN beta hbeta F :=
        calc
          (12 : ENNReal) * (γ * ENNReal.ofReal (variance F muWilson)) =
              (γ * ENNReal.ofReal (variance F muWilson)) * 12 := mul_comm _ _
          _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F * 12 :=
            mul_le_mul_left hGammaRef (12 : ENNReal)
          _ = (12 : ENNReal) *
                p4Q2BC_originalPhysicalTwelveColorHaarReference
                  H N hN beta hbeta F := mul_comm _ _
      _ = (12 : ENNReal) * ((12 : ENNReal)⁻¹ * sumRef) := rfl
      _ = sumRef := by
        calc
          (12 : ENNReal) * ((12 : ENNReal)⁻¹ * sumRef) =
              ((12 : ENNReal)⁻¹ * (12 : ENNReal)) * sumRef := by ac_rfl
          _ = sumRef := by
            rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hReal := ENNReal.toReal_mono hSumFinite hExact
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hVarNonneg] at hReal
  have hTwelveReal : (12 : ENNReal).toReal = (12 : ℝ) := by norm_num
  rw [hTwelveReal] at hReal
  have hRealAssoc :
      ((12 : ℝ) * γ.toReal) * variance F muWilson ≤ sumRef.toReal := by
    calc
      ((12 : ℝ) * γ.toReal) * variance F muWilson =
          (12 : ℝ) * (γ.toReal * variance F muWilson) := mul_assoc _ _ _
      _ ≤ sumRef.toReal := hReal
  change ((12 : ℝ) * γ.toReal) * variance F muWilson ≤ sumRef.toReal
  exact hRealAssoc

/-- Same EC coefficient reaches the entire true physical joint L². -/
theorem p4Q2EC_originalFullJointRieszQuadratic_maxColorCoefficient :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      ∀ x : J,
        p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
          ‖x - B x‖ ^ 2 ≤ Q x := by
  obtain ⟨m, M, hm, hM, hκ, hCoreRef⟩ :=
    p4Q2EC_originalUnnormalizedReference_maxColorWitness H N hN beta hbeta
  let κ : ℝ := p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M
  refine ⟨m, M, hm, hM, hκ, ?_⟩
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

local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "R" =>
  p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta

/-- Genuine quantitative stability of the ORIGINAL Wilson Riesz inverse
on the actual physical constant-orthogonal Hilbert space. The inverse
Lipschitz constant is exactly the reciprocal of the SAME explicit
finite-volume DQ/DF witness coefficient. No H-uniformity is asserted. -/
theorem p4Q2EC_originalRestrictedRiesz_maxColorAntilipschitz :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∃ c : ℝ≥0,
        0 < c ∧
        (c : ℝ) = p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
        AntilipschitzWith c⁻¹ R := by
  obtain ⟨m, M, hm, hM, hκ, hFull⟩ :=
    p4Q2EC_originalFullJointRieszQuadratic_maxColorCoefficient
      H N hN beta hbeta
  let κ : ℝ := p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M
  let c : ℝ≥0 := ⟨κ, hκ.le⟩
  have hc : 0 < c := by
    change (0 : ℝ) < κ
    exact hκ
  refine ⟨m, M, hm, hM, c, hc, rfl, ?_⟩
  apply ContinuousLinearMap.antilipschitz_of_forall_le_inner_map R hc
  intro x
  have hB : B (x : J) = 0 := by
    let W :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change W.starProjection (x : J) = 0
    exact (W.starProjection_apply_eq_zero_iff).2 x.property
  have hx := hFull (x : J)
  rw [hB, sub_zero] at hx
  have hRay : κ * ‖x‖ ^ 2 ≤ inner ℝ (R x) x := by
    change κ * ‖(x : J)‖ ^ 2 ≤ inner ℝ (A (x : J)) (x : J)
    rw [p4Q2BY_originalFullJointRieszOperator_quadratic]
    exact hx
  have hcoercive : ‖x‖ ^ 2 * (c : ℝ) ≤ inner ℝ (R x) x := by
    change ‖x‖ ^ 2 * κ ≤ inner ℝ (R x) x
    nlinarith [hRay]
  exact hcoercive.trans (by
    rw [Real.norm_eq_abs]
    exact le_abs_self _)

/-- EC coefficient in the actual self-adjoint original Wilson
Haar reference Riesz operator centered Loewner order. -/
theorem p4Q2EC_originalWilsonRiesz_maxColorLoewner :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M •
        p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta ≤ A := by
  obtain ⟨m, M, hm, hM, hκ, hDV⟩ :=
    p4Q2EC_originalFullJointRieszQuadratic_maxColorCoefficient
      H N hN beta hbeta
  let κ : ℝ := p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M
  refine ⟨m, M, hm, hM, hκ, ?_⟩
  let W : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  let C : J →L[ℝ] J :=
    p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta
  change (W - κ • C).IsPositive
  refine (ContinuousLinearMap.isPositive_iff (W - κ • C)).2 ⟨?_, ?_⟩
  · have hw : (W : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
    have hr : (C : J →ₗ[ℝ] J).IsSymmetric :=
      p4Q2DT_physicalCenteredResidualOperator_symmetric H N hN beta hbeta
    change ((W : J →ₗ[ℝ] J) - κ • (C : J →ₗ[ℝ] J)).IsSymmetric
    exact hw.sub (hr.smul (by simp))
  · intro x
    change 0 ≤ inner ℝ ((W - κ • C) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    have hW : inner ℝ (W x) x = Q x :=
      p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta x
    have hR : inner ℝ (C x) x = ‖x - B x‖ ^ 2 :=
      p4Q2DT_physicalCenteredResidualOperator_inner_self H N hN beta hbeta x
    rw [hW, hR]
    exact sub_nonneg.mpr (hDV x)

end OriginalWilson
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EC_DZCoefficient_le_originalSharpMaxColor
#print axioms MGAP4D.MathlibAnalytic.p4Q2EC_originalNormalizedReference_maxColorWitness
#print axioms MGAP4D.MathlibAnalytic.p4Q2EC_originalFullJointRieszQuadratic_maxColorCoefficient
#print axioms MGAP4D.MathlibAnalytic.p4Q2EC_originalRestrictedRiesz_maxColorAntilipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2EC_originalWilsonRiesz_maxColorLoewner
