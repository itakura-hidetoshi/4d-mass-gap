import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroProductLawBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionIdempotent
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Replacements at two distinct physical links commute exactly. -/
theorem compact_oriented_replaceLink_comm_of_ne
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (g h : L.Gauge)
    (hNe : target ≠ source) :
    L.replaceLink (L.replaceLink A target g) source h =
      L.replaceLink (L.replaceLink A source h) target g := by
  funext edge
  by_cases hTarget : edge = target
  · subst edge
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hNe]
  · by_cases hSource : edge = source
    · subst edge
      simp [CompactOrientedGaugeWilsonSystem.replaceLink, hNe.symm]
    · simp [CompactOrientedGaugeWilsonSystem.replaceLink, hTarget, hSource]

/-- At zero coupling, one-link heat-bath projection is literal normalized Haar
averaging in the selected physical-link coordinate. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjection target f A =
      ∫ g, f (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_normalizedCompactHaar_of_beta_eq_zero
    C hBeta A target]

/-- At zero Wilson coupling, exact one-link heat-bath projections at two
distinct coordinates commute on every bounded continuous observable.  The proof
is the product-Haar Fubini interchange together with exact commutation of the
two coordinate replacements. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_comm_of_beta_eq_zero_of_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (hNe : target ≠ source)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection source O) =
      C.singleLinkHeatBathProjection source
        (C.singleLinkHeatBathProjection target O) := by
  funext A
  let μ : Measure C.base.Gauge := normalizedCompactHaar C.base.Gauge
  let F : C.base.Gauge × C.base.Gauge → ℝ := fun z =>
    O (C.base.replaceLink
      (C.base.replaceLink A target z.1) source z.2)
  have hFirst : Continuous (fun z : C.base.Gauge × C.base.Gauge =>
      C.base.replaceLink A target z.1) :=
    (continuous_compact_oriented_replaceLink C A target).comp continuous_fst
  have hInput : Continuous (fun z : C.base.Gauge × C.base.Gauge =>
      (C.base.replaceLink A target z.1, z.2)) :=
    hFirst.prodMk continuous_snd
  have hReplace : Continuous (fun z : C.base.Gauge × C.base.Gauge =>
      C.base.replaceLink
        (C.base.replaceLink A target z.1) source z.2) :=
    (continuous_compact_oriented_replaceLink_uncurry C source).comp hInput
  have hFContinuous : Continuous F := by
    exact O.continuous.comp hReplace
  have hFIntegrable : Integrable F (μ.prod μ) := by
    exact hFContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
    C hBeta target (C.singleLinkHeatBathProjection source O) A]
  calc
    (∫ g,
        C.singleLinkHeatBathProjection source O
          (C.base.replaceLink A target g) ∂μ) =
      ∫ g, ∫ h, F (g, h) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
          C hBeta source O (C.base.replaceLink A target g)]
    _ = ∫ h, ∫ g, F (g, h) ∂μ ∂μ := by
      exact integral_integral_swap hFIntegrable
    _ = ∫ h, ∫ g,
        O (C.base.replaceLink
          (C.base.replaceLink A source h) target g) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with h
      apply integral_congr_ae
      filter_upwards [] with g
      exact congrArg O
        (compact_oriented_replaceLink_comm_of_ne
          C.base A target source g h hNe)
    _ = ∫ h,
        C.singleLinkHeatBathProjection target O
          (C.base.replaceLink A source h) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with h
      rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
        C hBeta target O (C.base.replaceLink A source h)]
    _ = C.singleLinkHeatBathProjection source
        (C.singleLinkHeatBathProjection target O) A := by
      rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
        C hBeta source (C.singleLinkHeatBathProjection target O) A]

/-- The entire finite family of zero-coupling coordinate heat-bath projections
commutes pairwise on the bounded-continuous core, including the diagonal case by
idempotence. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_pairwise_comm_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection source O) =
      C.singleLinkHeatBathProjection source
        (C.singleLinkHeatBathProjection target O) := by
  by_cases hEq : target = source
  · subst source
    rfl
  · exact
      continuous_compact_oriented_singleLinkHeatBathProjection_comm_of_beta_eq_zero_of_ne
        C hBeta target source hEq O

/-- Actual side-three periodic `SU(2)` one-link heat-bath projections commute
pairwise on every bounded continuous observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathProjection_pairwise_comm
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (O : BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          source O) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          target O) := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_pairwise_comm_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target source O

/-- Compact proof-facing receipt for the first operator-theoretic consequence of
the actual beta-zero product law.  Full `L²` tensorization still requires the
closure/density lift and identification of the total coordinate average with the
vacuum projection. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationReceipt :
    Prop :=
  ∀ (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (O : BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          source O) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          target O)

/-- The actual zero-coupling coordinate-projection commutation receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionCommutationReceipt := by
  intro target source O
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathProjection_pairwise_comm
      target source O

end

end MathlibAnalytic
end MGAP4D
