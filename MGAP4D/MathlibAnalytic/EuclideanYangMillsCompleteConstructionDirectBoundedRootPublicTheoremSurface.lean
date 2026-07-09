import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPI
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Theorem-facing downstream surface for the complete Yang--Mills direct bounded
root public API.

This file only decomposes the already exposed public full spectral package and
route markers into stable theorem names.  It does not add a new spectral theorem,
spectral projection construction, numerical lower bound, or final Yang--Mills
mass-gap claim.
-/

/-- The full spectral package exposed through the stable root public API. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E) ∧
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralPackage S

/-- The stable root public API exposes the mass-gap proposition carried by the
complete construction certificate. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicHasMassGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S).1

/-- The stable root public API exposes positivity of the adopted exact gap real. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicExactGapPositive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S).2.1

/-- The stable root public API exposes the exact-gap infimum identity. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicExactGapInfimum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S).2.2.1

/-- The stable root public API exposes the spectral lower-bound witness package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicSpectralLowerWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S).2.2.2.1

/-- The stable root public API exposes the first-excitation spectral witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFirstExcitationWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S).2.2.2.2

/-- Route markers exposed as a theorem-facing package through the root public API. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkerTheoremSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkers S).2.1,
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkers S).2.2,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicEndpointNames S⟩

/-- Complete downstream theorem surface: the public root API gives the full
spectral package together with the direct bounded route-marker package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompleteTheoremSurface
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
    ((euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ]) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralTheoremSurface S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkerTheoremSurface S⟩

end

end MathlibAnalytic
end MGAP4D