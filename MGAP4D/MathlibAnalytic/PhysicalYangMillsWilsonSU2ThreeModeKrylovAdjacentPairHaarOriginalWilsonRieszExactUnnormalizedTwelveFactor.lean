import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExplicitFiniteVolumeCertificate
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-DZ: EXACT unnormalized twelve-color Wilson Haar Riesz certificate

DY compares true Wilson variance to the normalized original twelve-color
Haar reference and then uses the lossy average <= sum. The ACTUAL original
Haar Riesz quadratic is the unnormalized 12-color SUM. Here multiplication
of the original normalized ENNReal inequality by the actual factor 12
cancels the exact 1/12 normalization and yields an improved certificate
  kappa_DZ(H,beta,m,M) = 12 * kappa_DY(H,beta,m,M) > kappa_DY > 0
for the SAME genuinely physical original Wilson DQ/DF witnesses m,M.

Prove the improved concrete bound, true full physical joint L² coercivity,
original physical Riesz Loewner bound, and quantitative restricted inverse
stability. No new physical law, mean identification, D12 substitution,
positive-beta commutation, or H-uniform/continuum Yang--Mills gap is
asserted. The inverse spatial-link-cardinality remains in kappa_DY.
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

local instance p4Q2DZ_constantLineHasOrthogonalProjection :
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

/-- The original unnormalized 12-color sum retains exactly twelve
times the DY coefficient for the SAME genuine Wilson DQ/DF m,M witnesses. -/
noncomputable def p4Q2DZ_originalUnnormalizedRieszCoefficient (m M : ℝ) : ℝ :=
  (12 : ℝ) * p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M

theorem p4Q2DZ_originalUnnormalizedCoefficient_pos
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) :
    0 < p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M := by
  unfold p4Q2DZ_originalUnnormalizedRieszCoefficient
  exact mul_pos (by norm_num)
    (p4Q2DY_originalRieszFiniteVolumeCoefficient_pos H beta m M hm hM)

theorem p4Q2DZ_originalUnnormalizedCoefficient_gt_DY
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) :
    p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M <
      p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M := by
  have hκ := p4Q2DY_originalRieszFiniteVolumeCoefficient_pos H beta m M hm hM
  unfold p4Q2DZ_originalUnnormalizedRieszCoefficient
  nlinarith

/-- Exact original normalized reference to UNNORMALIZED Haar sum, without
the earlier lossy estimate normalized <= sum. Same original DQ/DF m,M. -/
theorem p4Q2DZ_originalWilsonUnnormalizedReference_exactTwelveWitness :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M ∧
      ∀ (F : Joint → ℝ) (_hF : StronglyMeasurable F)
        (bound : ℝ) (_hbound : ∀ z, ‖F z‖ ≤ bound),
        p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M *
            variance F muWilson ≤
          p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
            H N hN beta hbeta F := by
  obtain ⟨m, M, hm, hM, hNorm⟩ :=
    p4Q2DY_originalNormalizedReference_explicitVarianceWitness
      H N hN beta hbeta
  let k : ENNReal :=
    p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
      (ENNReal.ofReal (M + 1))⁻¹
  let γ : ENNReal := min k 1
  have hPos : 0 < p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M :=
    p4Q2DZ_originalUnnormalizedCoefficient_pos H beta m M hm hM
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
        mul_le_mul_left hGammaRef (12 : ENNReal)
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
  change (12 : ℝ) * γ.toReal * variance F muWilson ≤
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F at hReal
  change p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M *
      variance F muWilson ≤
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F
  exact hReal

local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- The exact improved unnormalized coefficient extends by genuine BW density
and BX continuity to the ACTUAL full original Wilson joint L². -/
theorem p4Q2DZ_originalFullJointRieszQuadratic_exactTwelveCoefficient :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M ∧
      ∀ x : J,
        p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M *
          ‖x - B x‖ ^ 2 ≤ Q x := by
  obtain ⟨m, M, hm, hM, hκ, hCoreRef⟩ :=
    p4Q2DZ_originalWilsonUnnormalizedReference_exactTwelveWitness H N hN beta hbeta
  let κ : ℝ := p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M
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
theorem p4Q2DZ_originalRestrictedRiesz_exactTwelveAntilipschitz :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∃ c : ℝ≥0,
        0 < c ∧
        (c : ℝ) = p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M ∧
        AntilipschitzWith c⁻¹ R := by
  obtain ⟨m, M, hm, hM, hκ, hFull⟩ :=
    p4Q2DZ_originalFullJointRieszQuadratic_exactTwelveCoefficient
      H N hN beta hbeta
  let κ : ℝ := p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M
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

/-- Genuine original Wilson physical Riesz Loewner coercivity with
the same EXACT unnormalized 12-color m,M witness. -/
theorem p4Q2DZ_originalWilsonRiesz_exactTwelveLoewner :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M ∧
      p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M •
        p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta ≤ A := by
  obtain ⟨m, M, hm, hM, hκ, hDV⟩ :=
    p4Q2DZ_originalFullJointRieszQuadratic_exactTwelveCoefficient
      H N hN beta hbeta
  let κ : ℝ := p4Q2DZ_originalUnnormalizedRieszCoefficient H beta m M
  refine ⟨m, M, hm, hM, hκ, ?_⟩
  let W : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  let R : J →L[ℝ] J :=
    p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta
  change (W - κ • R).IsPositive
  refine (ContinuousLinearMap.isPositive_iff (W - κ • R)).2 ⟨?_, ?_⟩
  · have hw : (W : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
    have hr : (R : J →ₗ[ℝ] J).IsSymmetric :=
      p4Q2DT_physicalCenteredResidualOperator_symmetric H N hN beta hbeta
    change ((W : J →ₗ[ℝ] J) - κ • (R : J →ₗ[ℝ] J)).IsSymmetric
    exact hw.sub (hr.smul (by simp))
  · intro x
    change 0 ≤ inner ℝ ((W - κ • R) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    have hW : inner ℝ (W x) x = Q x :=
      p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta x
    have hR : inner ℝ (R x) x = ‖x - B x‖ ^ 2 :=
      p4Q2DT_physicalCenteredResidualOperator_inner_self H N hN beta hbeta x
    rw [hW, hR]
    exact sub_nonneg.mpr (hDV x)

end OriginalWilson
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2DZ_originalWilsonUnnormalizedReference_exactTwelveWitness
#print axioms MGAP4D.MathlibAnalytic.p4Q2DZ_originalFullJointRieszQuadratic_exactTwelveCoefficient
#print axioms MGAP4D.MathlibAnalytic.p4Q2DZ_originalRestrictedRiesz_exactTwelveAntilipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2DZ_originalWilsonRiesz_exactTwelveLoewner
