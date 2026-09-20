import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import Mathlib.Tactic

/-!
# Canonical fixed-right response resolvent

This file connects the canonical actual-response profile to the terminal-free
response-controlled resolvent.

The canonical profile is pointwise minimal among all nonnegative uniform
response profiles. Consequently any weighted-column certificate proved for an
auxiliary uniform profile descends automatically to the canonical profile.

Finally, if the canonical profile itself has a target-centered weighted-column
coefficient M with the response-controlled coefficient strictly below one,
then its remote entries satisfy the terminal-free resolvent bound from the
literal actual responses. This is a genuine statement about the canonical
actual response, not an arbitrary assumed profile.

No existence of such an M is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance canonicalFixedRightResponseResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical actual-response profile is pointwise minimal among all
nonnegative profiles that uniformly dominate every literal fixed-right
response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_of_uniformBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      R target source := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hSup : sSup S ≤ R target source := by
    apply csSup_le
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
          H N hN beta hbeta target source
    · intro x hx
      rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
      exact hResponse B target source g₁ g₂ h k
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
  exact max_le (hRNonneg target source) hSup

/-- A target-centered weighted-column certificate for any nonnegative uniform
response profile descends to the canonical actual-response profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_of_uniformBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 0 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center R responseCoefficient) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
      H s center
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      responseCoefficient := by
  intro source
  have hPoint :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target ≤
          R target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target := by
    intro target
    exact mul_le_mul_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_of_uniformBound
        H N hN beta hbeta R hRNonneg hResponse target source)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hs center target)
  exact
    (Finset.sum_le_sum fun target _ => hPoint target).trans
      (hWeighted source)

/-- Under a strict canonical weighted-column hypothesis, the canonical actual
remote response itself satisfies the response-controlled weighted resolvent
bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_responseControlledWeightedResolvent_of_remote
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
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
      0 < 1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient := by
    linarith
  have hKNonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
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
            H N hN beta hbeta B target source g₁ g₂ h k ≤ K := by
    intro B g₁ g₂ h k
    simpa [R, K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_responseControlledWeightedResolvent_of_remote
        H N hN beta hbeta s hs R hRNonneg hUniform
        responseCoefficient hResponseCoefficient B hne hNoShare
        (by simpa [R] using hResponseWeighted)
        hCoefficientLtOne g₁ g₂ h k
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
