import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCoordinateProjectionCommutationBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalVarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

private theorem continuous_compact_oriented_bcf_abs_le_norm_l2_comm
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- On the canonical bounded-continuous Gibbs `L²` core, the two iterated
zero-coupling one-link conditional-expectation projections agree.  The proof
uses the exact concrete BCF commutation theorem and the existing identification
of each abstract `condExpL2` projection with its concrete Haar-kernel action. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_comm_on_gibbsL2RepresentativeBCF_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionL2 target
        (C.singleLinkHeatBathProjectionL2 source
          (C.gibbsL2RepresentativeBCF O)) =
      C.singleLinkHeatBathProjectionL2 source
        (C.singleLinkHeatBathProjectionL2 target
          (C.gibbsL2RepresentativeBCF O)) := by
  let M : ℝ := ‖O‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOStrong : StronglyMeasurable
      (O : C.base.Configuration → ℝ) :=
    O.continuous.stronglyMeasurable
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    dsimp [M]
    exact continuous_compact_oriented_bcf_abs_le_norm_l2_comm O A
  have hSourceStrong : StronglyMeasurable
      (C.singleLinkHeatBathProjection source O) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C source O hOStrong
  have hSourceBound :
      ∀ A, |C.singleLinkHeatBathProjection source O A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C source O hOStrong M hM0 hOBound
  have hTargetStrong : StronglyMeasurable
      (C.singleLinkHeatBathProjection target O) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target O hOStrong
  have hTargetBound :
      ∀ A, |C.singleLinkHeatBathProjection target O A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target O hOStrong M hM0 hOBound
  have hTargetSourceStrong : StronglyMeasurable
      (C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection source O)) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target (C.singleLinkHeatBathProjection source O) hSourceStrong
  have hTargetSourceBound :
      ∀ A,
        |C.singleLinkHeatBathProjection target
          (C.singleLinkHeatBathProjection source O) A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target (C.singleLinkHeatBathProjection source O)
      hSourceStrong M hM0 hSourceBound
  have hSourceTargetStrong : StronglyMeasurable
      (C.singleLinkHeatBathProjection source
        (C.singleLinkHeatBathProjection target O)) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C source (C.singleLinkHeatBathProjection target O) hTargetStrong
  have hSourceTargetBound :
      ∀ A,
        |C.singleLinkHeatBathProjection source
          (C.singleLinkHeatBathProjection target O) A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C source (C.singleLinkHeatBathProjection target O)
      hTargetStrong M hM0 hTargetBound
  have hSource :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C source O hOStrong M hM0 hOBound
  have hTarget :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target O hOStrong M hM0 hOBound
  have hTargetSource :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target (C.singleLinkHeatBathProjection source O)
      hSourceStrong M hM0 hSourceBound
  have hSourceTarget :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C source (C.singleLinkHeatBathProjection target O)
      hTargetStrong M hM0 hTargetBound
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF
  rw [hSource, hTarget, hTargetSource, hSourceTarget]
  apply Lp.ext
  filter_upwards
    [(continuous_compact_oriented_memLp_two_of_uniform_bound
      C
      (C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection source O))
      hTargetSourceStrong M hM0 hTargetSourceBound).coeFn_toLp,
     (continuous_compact_oriented_memLp_two_of_uniform_bound
      C
      (C.singleLinkHeatBathProjection source
        (C.singleLinkHeatBathProjection target O))
      hSourceTargetStrong M hM0 hSourceTargetBound).coeFn_toLp] with A hLeft hRight
  rw [hLeft, hRight]
  exact congrFun
    (continuous_compact_oriented_singleLinkHeatBathProjection_pairwise_comm_of_beta_eq_zero
      C hBeta target source O) A

/-- At zero Wilson coupling, all exact one-link heat-bath orthogonal projections
commute pairwise on the full Gibbs `L²` Hilbert space.  Equality on the canonical
bounded-continuous representatives extends to every `L²` vector because
bounded continuous functions have dense range in finite-measure `L²`, while both
iterated projections are continuous. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target
        (C.singleLinkHeatBathProjectionL2 source f) =
      C.singleLinkHeatBathProjectionL2 source
        (C.singleLinkHeatBathProjectionL2 target f) := by
  let p : Lp ℝ 2 C.gibbsMeasure → Prop := fun q =>
    C.singleLinkHeatBathProjectionL2 target
        (C.singleLinkHeatBathProjectionL2 source q) =
      C.singleLinkHeatBathProjectionL2 source
        (C.singleLinkHeatBathProjectionL2 target q)
  apply DenseRange.induction_on (p := p)
    (BoundedContinuousFunction.toLp_denseRange
      ℝ C.gibbsMeasure ℝ (by norm_num)) f
  · apply isClosed_eq
    · exact
        (C.singleLinkHeatBathProjectionL2 target).continuous.comp
          (C.singleLinkHeatBathProjectionL2 source).continuous
    · exact
        (C.singleLinkHeatBathProjectionL2 source).continuous.comp
          (C.singleLinkHeatBathProjectionL2 target).continuous
  · intro O
    change p
      (BoundedContinuousFunction.toLp 2 C.gibbsMeasure ℝ O)
    simpa [p,
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF] using
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_comm_on_gibbsL2RepresentativeBCF_of_beta_eq_zero
        C hBeta target source O

/-- The actual side-three periodic `SU(2)` endpoint system has a pairwise
commuting family of all `324` one-link heat-bath projections on its full Gibbs
`L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathProjectionL2_pairwise_comm
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          source f) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          target f) := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target source f

/-- Compact receipt for the full-`L²` pairwise commutation layer.  This does not
identify the product of all coordinate projections with the vacuum projection
and does not yet assert variance tensorization or the `323/324` random-scan
bound. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationL2Receipt :
    Prop :=
  ∀ (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          source f) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          target f)

/-- The actual beta-zero full-`L²` coordinate-projection commutation receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationL2Receipt := by
  intro target source f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathProjectionL2_pairwise_comm
      target source f

end

end MathlibAnalytic
end MGAP4D
