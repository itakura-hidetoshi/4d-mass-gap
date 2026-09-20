import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledAsymptoticResponse
import Mathlib.Tactic

/-!
# Pin-free canonical fixed-right response resolvent

The canonical fixed-right response profile is the pointwise `sSup` of all
literal target-ratio responses and therefore uniformly dominates every actual
response while remaining pointwise minimal among such profiles.

The distinguished-target pin has now been removed from the physical
response-controlled kernel and from the complete stationary/asymptotic route.
This file transports the merged asymptotic theorem to the canonical response
profile.

Under a target-centered weighted-column certificate with coefficient `M` and

  18 * eta(beta) * s^2 + exp(16 * beta) * M < 1,

the canonical remote response obeys the pin-free weighted resolvent bound.
There is no standalone `eta(beta)` term.

This theorem is still a conditional resolvent interface.  It does not assume
or claim that the canonical weighted response coefficient has already been
closed self-consistently.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance pinFreeCanonicalFixedRightResponseResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Under a strict canonical weighted-column hypothesis, the canonical actual
remote response satisfies the pin-free response-controlled weighted resolvent
bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_pinFreeResponseControlledWeightedResolvent_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹
  have hRNonneg : ∀ t q, 0 ≤ R t q := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta
  have hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
        H N hN beta hbeta
  have hOneSub :
      0 <
        1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient := by
    linarith
  have hKNonneg : 0 ≤ K := by
    dsimp [K]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant_self_nonneg
              H beta hbeta source)
            (Real.exp_pos _).le)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
            H s (le_trans (by norm_num) hs) target source))
        (inv_nonneg.mpr hOneSub.le)
  have hAll :
      ∀
        (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k ≤
          K := by
    intro B g₁ g₂ h k
    simpa [R, K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_pinFreeWeightedResolvent_of_remote
        H N hN beta hbeta s hs R hRNonneg hUniform
        responseCoefficient hResponseCoefficient target source
        (by simpa [R] using hResponseWeighted)
        hCoefficientLtOne B hne hNoShare g₁ g₂ h k
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hSup : sSup S ≤ K := by
    apply csSup_le
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
          H N hN beta hbeta target source
    · intro x hx
      rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
      exact hAll B g₁ g₂ h k
  change max 0 (sSup S) ≤ K
  exact max_le hKNonneg hSup

end

end MathlibAnalytic
end MGAP4D
