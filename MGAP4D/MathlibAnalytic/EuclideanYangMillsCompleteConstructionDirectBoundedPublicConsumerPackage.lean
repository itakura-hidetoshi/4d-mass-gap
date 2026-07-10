import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedFirstExcitationConsumerPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Public consumer package for the complete Yang--Mills direct bounded route.

This layer joins the certified spectral consumer facts with the public direct
bounded API markers.  It is meant to provide a compact downstream theorem for
callers that need both the mathematical certificate surface and the route/API
receipts.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- The public consumer proposition: certified spectral facts plus public route
receipts for downstream consumers. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackageProp
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
        "compatibility-only"

/-- Certified spectral facts plus public route receipts for downstream consumers. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackageProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapValue_ne_zero S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_orderWitnessConsumer S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_endpointNames S,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).2⟩

/-- The public consumer package paired with the certified nonzero-spectrum subset
chain. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackageProp S ∧
      (∃ δ : ℝ, 0 < δ ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | δ ≤ E} ∧
        {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} ∧
        {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 ≤ E} ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | 0 < E} ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | 0 ≤ E})

/-- Public consumer package paired with the previously certified nonzero-spectrum
subset-chain theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChain
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S,
    euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_subset_chain S⟩

end

end MathlibAnalytic
end MGAP4D
