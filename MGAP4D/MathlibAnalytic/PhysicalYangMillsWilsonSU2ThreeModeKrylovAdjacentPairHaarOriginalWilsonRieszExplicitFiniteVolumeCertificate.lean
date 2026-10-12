import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszSpectralBandAndIsUnit
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-DY: genuine original Wilson Riesz explicit finite-volume coefficient

DV established existence of a positive original full-physical-Wilson-joint-L²
Haar-reference Riesz coefficient. Here the EXISTING genuinely physical DQ
original Wilson Haar fiber mass witness m and DF Wilson/pair-Haar variance
comparison witness M are exposed as typed Lean witnesses, together with
the EXACT coefficient:
  kappa(H,N,beta;m,M)
    = (min ((m * exp(-32 beta) / (12 * spatialLinkCard(H))) / (M+1)) 1).toReal,
where the actual implementation preserves ENNReal normalization at all
steps, by reusing p4Q2DQ_allLinkHilbertFloorCoefficient.

The SAME explicit positive coefficient is propagated from genuine original
normalized Wilson Haar reference and Wilson variance, through the literal
UNNORMALIZED original Haar reference, to its continuous whole physical L²
Riesz quadratic, using the actual BW/BX dense core.

Additionally, on the actual physical constant-orthogonal Hilbert sector
we prove a quantitative ANTILIPSCHITZ inverse-stability certificate with
this SAME explicit coefficient using pinned mathlib's coercivity theorem.

No synthetic physical measure, new axiom, D12 identification, or H-uniform
coefficient is asserted. In fact the explicit formula RETAINS an inverse
spatial-link-cardinality factor and finite-volume physical m, M witnesses.
Original signed fine/frozen Krylov, C1/C2/C3 and continuum H2/H3/H4 remain open.
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

local instance p4Q2DY_constantLineHasOrthogonalProjection :
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

/-- Typed, genuinely physical, unoptimized finite-volume coefficient.
DQ's actual link-count denominator and original Wilson mass floor m, and
DF's actual upper variance-comparison factor M, are retained verbatim.
The truncation at 1 matches the original DV ENNReal-to-real argument. -/
noncomputable def p4Q2DY_originalRieszFiniteVolumeCoefficient
    (m M : ℝ) : ℝ :=
  (min
    (p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
      (ENNReal.ofReal (M + 1))⁻¹)
    1).toReal

/-- Its physical DQ/DF witness inputs imply strict positivity at fixed
finite volume. It is NOT uniformly positive as H varies from this proof. -/
theorem p4Q2DY_originalRieszFiniteVolumeCoefficient_pos
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) :
    0 < p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M := by
  let a : ENNReal := p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
  let b : ENNReal := ENNReal.ofReal (M + 1)
  let k : ENNReal := a * b⁻¹
  have _hPhysicalUpperPos : 0 < M + 1 := by linarith
  have ha : 0 < a :=
    p4Q2DQ_allLinkHilbertFloorCoefficient_pos H beta m hm
  have hbTop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hk : 0 < k :=
    (ENNReal.mul_pos_iff).2 ⟨ha, ENNReal.inv_pos.mpr hbTop⟩
  have hγ : 0 < min k 1 := lt_min hk (by norm_num)
  have hγTop : min k 1 ≠ ∞ := ne_of_lt
    (lt_of_le_of_lt (min_le_right k (1 : ENNReal)) (by norm_num))
  change 0 < (min k 1).toReal
  exact ENNReal.toReal_pos hγ.ne' hγTop

/-- Exact ACTUAL DQ/DF finite-volume witness for the lower comparison
between the ORIGINAL normalized Wilson Haar reference and Wilson variance.
The witnesses are exposed in the theorem type rather than hidden behind
an existential coefficient. -/
theorem p4Q2DY_originalNormalizedReference_explicitVarianceWitness :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F),
        ∀ (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
          (f : JH), F =ᵐ[muPair] (f : Joint → ℝ) →
            (p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
                (ENNReal.ofReal (M + 1))⁻¹) *
                ENNReal.ofReal (variance F muWilson) ≤
              p4Q2BC_originalPhysicalTwelveColorHaarReference
                H N hN beta hbeta F := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2DQ_originalWilsonTwelveReference_ge_allCoordinateHilbertDefects
      H N hN beta hbeta
  obtain ⟨_mW, M, _hmW, hM, hVariance⟩ :=
    p4Q2DF_originalWilsonJoint_allBoundedVariance_uniform_sandwich
      H N hN beta hbeta
  let a : ENNReal := p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
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

/-- The EXACT same explicit mass/variance witness survives conversion
from the normalized ENNReal Haar reference to the real UNNORMALIZED literal
original twelve-color Haar reference, with no physical D12 substitution. -/
theorem p4Q2DY_originalReferenceReal_explicitVarianceWitness :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M ∧
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F)
        (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
          p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M *
              variance F muWilson ≤
            p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
              H N hN beta hbeta F := by
  obtain ⟨m, M, hm, hM, hNormalized⟩ :=
    p4Q2DY_originalNormalizedReference_explicitVarianceWitness
      H N hN beta hbeta
  let k : ENNReal :=
    p4Q2DQ_allLinkHilbertFloorCoefficient H beta m *
      (ENNReal.ofReal (M + 1))⁻¹
  have hk : 0 < k := by
    have ha : 0 < p4Q2DQ_allLinkHilbertFloorCoefficient H beta m :=
      p4Q2DQ_allLinkHilbertFloorCoefficient_pos H beta m hm
    exact (ENNReal.mul_pos_iff).2
      ⟨ha, ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top⟩
  let γ : ENNReal := min k 1
  have hγPos : 0 < γ := lt_min hk (by norm_num)
  have hγTop : γ ≠ ∞ := ne_of_lt
    (lt_of_le_of_lt (min_le_right k (1 : ENNReal)) (by norm_num))
  have hγReal : 0 < γ.toReal :=
    ENNReal.toReal_pos hγPos.ne' hγTop
  have hκPos : 0 < p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M := by
    change 0 < γ.toReal
    exact hγReal
  refine ⟨m, M, hm, hM, hκPos, ?_⟩
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
  change γ.toReal * variance F muWilson ≤
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta F
  exact hReal

/-- GENUINE original Wilson full physical joint L² quantitative
coercivity with the SAME explicit DQ/DF mass/variance certificate coefficient.
BW's actual bounded-core density and BX's full-L² continuity allow no loss. -/
theorem p4Q2DY_originalFullJointRieszQuadratic_explicitCoefficient :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M ∧
      ∀ x : J,
        p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M *
          ‖x - B x‖ ^ 2 ≤ Q x := by
  obtain ⟨m, M, hm, hM, hκ, hCoreRef⟩ :=
    p4Q2DY_originalReferenceReal_explicitVarianceWitness H N hN beta hbeta
  let κ : ℝ := p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M
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
theorem p4Q2DY_originalRestrictedRiesz_explicitAntilipschitz :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∃ c : ℝ≥0,
        0 < c ∧
        (c : ℝ) = p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M ∧
        AntilipschitzWith c⁻¹ R := by
  obtain ⟨m, M, hm, hM, hκ, hFull⟩ :=
    p4Q2DY_originalFullJointRieszQuadratic_explicitCoefficient
      H N hN beta hbeta
  let κ : ℝ := p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M
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

end OriginalWilson
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2DY_originalNormalizedReference_explicitVarianceWitness
#print axioms MGAP4D.MathlibAnalytic.p4Q2DY_originalFullJointRieszQuadratic_explicitCoefficient
#print axioms MGAP4D.MathlibAnalytic.p4Q2DY_originalRestrictedRiesz_explicitAntilipschitz
