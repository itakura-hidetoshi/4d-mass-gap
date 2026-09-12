import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Spectral downstream package for the complete Yang--Mills direct bounded route.

This file connects the downstream theorem package to the complete-construction
spectral certificate surface.  It extracts the already-proved full spectral
package from the complete direct bounded certificate and pairs it with the
stable downstream theorem package from the public API route.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- The downstream theorem package is compatible with the complete construction
full spectral package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E) ∧
      ∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)) ∧
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact ⟨
    euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_endpointNames S,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).2⟩

/-- Downstream projection of the mass-gap predicate from the complete spectral
package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C).1

/-- Downstream projection of the positive exact-gap witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C).2.1

/-- Downstream projection of the exact-gap spectral formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C).2.2.1

/-- Downstream projection of the spectral lower-bound witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C).2.2.2.1

/-- Downstream projection of the first-excitation spectral witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C).2.2.2.2

/-- Combined downstream theorem package: spectral facts plus public direct bounded
route markers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)) ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status S,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).1⟩

end

end MathlibAnalytic
end MGAP4D
