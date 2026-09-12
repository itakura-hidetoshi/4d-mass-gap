import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerAccessors
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Public consumer endpoint theorems for the complete Yang--Mills direct bounded
route.

This file consumes the public consumer accessor layer and exposes compact
endpoint theorems that downstream files can use without destructuring the large
public consumer package directly.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Endpoint proposition for the main public consumer spectral facts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal ≠ 0 ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ))

/-- Endpoint theorem for the main public consumer spectral facts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_positiveExactGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_exactGap_ne_zero S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_lowerBoundOrderWitness S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_firstExcitationWitness S⟩

/-- Endpoint proposition for public route receipts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility" ∧
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" ∧
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only"

/-- Endpoint theorem for public route receipts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceipts
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_endpointNames S,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).2⟩

/-- Endpoint theorem pairing spectral consumer facts with route receipts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceipts S⟩

/-- Endpoint theorem pairing the public consumer package with its subset-chain
certificate. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint_withSubsetChain
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChain S⟩

end

end MathlibAnalytic
end MGAP4D
