import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDirectBoundedPublicHandoff
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Complete Yang--Mills construction certificate with the direct bounded R4 operator
handoff.

The finite-volume/continuum construction spine already supplies the measure,
OS/Wightman, Hamiltonian/PVM, and spectral certificate.  This file records the
next public handoff: the complete construction surface consumes the direct
bare-`M` boundedness API as the primary R4 operator route, while keeping the
route-backed names compatibility-only.
-/

/-- Complete construction certificate bundled with the direct bounded R4 operator
public handoff. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  constructionCertificate :
    EuclideanYangMillsContinuumMeasureConstructionCertificate S
  publicHandoffStatus : String
  publicHandoffStatus_eq :
    publicHandoffStatus =
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status
  primaryBoundedRoute_eq :
    EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle"
  routeBackedRole_eq :
    EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only"
  directEndpointNames : List String
  directEndpointNames_eq :
    directEndpointNames =
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names
  fullSpectralPackage :
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
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)

/-- Build the complete construction certificate and attach the direct bounded R4
operator public handoff. -/
def euclideanYangMillsCompleteConstructionDirectBoundedCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S :=
  { constructionCertificate :=
      euclideanYangMillsContinuumMeasureConstructionCertificate S
    publicHandoffStatus :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status
    publicHandoffStatus_eq := rfl
    primaryBoundedRoute_eq :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route_is_direct
    routeBackedRole_eq :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_is_compatibility_only
    directEndpointNames :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names
    directEndpointNames_eq := rfl
    fullSpectralPackage :=
      euclidean_yang_mills_continuum_spine_certificate_full_spectral_package S
        (euclideanYangMillsContinuumMeasureConstructionCertificate S) }

/-- The complete construction certificate exposes the same full spectral package
as the construction spine certificate. -/
theorem euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S) :
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
  exact C.fullSpectralPackage

/-- The complete construction certificate exposes the direct bounded R4 operator
public handoff in one theorem-level package. -/
theorem euclidean_yang_mills_complete_construction_direct_bounded_public_handoff
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (C : EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S) :
    C.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      EuclideanYangMillsR4HilbertReconstructionQuotient.
          r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      EuclideanYangMillsR4HilbertReconstructionQuotient.
          r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" ∧
      C.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact ⟨
    by
      rw [C.publicHandoffStatus_eq]
      exact EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status_eq,
    C.primaryBoundedRoute_eq,
    C.routeBackedRole_eq,
    by
      rw [C.directEndpointNames_eq]
      exact EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names_eq⟩

/-- End-to-end complete construction surface: spectral package plus the direct
bounded R4 operator handoff marker. -/
theorem euclidean_yang_mills_complete_construction_direct_bounded_package
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
    EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" ∧
    EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only" ∧
    EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  let C := euclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  exact ⟨
    euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S C,
    C.primaryBoundedRoute_eq,
    C.routeBackedRole_eq,
    by
      exact EuclideanYangMillsR4HilbertReconstructionQuotient.
        r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names_eq⟩

end

end MathlibAnalytic
end MGAP4D
