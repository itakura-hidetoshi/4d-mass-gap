import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerSmoke
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Compact downstream API for the public consumer endpoint of the complete
Yang--Mills direct bounded route.

This file packages the smoke certificates, endpoint theorem, route receipts,
and subset-chain consumer theorem into compact downstream API theorems.  It is a
consumer of the certified theorem surface, not a documentation-only layer.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Compact downstream API proposition for public consumer facts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerCompactAPIProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSmokeProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S

/-- Compact downstream API theorem for public consumer facts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerCompactAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerCompactAPIProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSmoke S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint S⟩

/-- Compact downstream API proposition including route receipts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteAPIProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerCompactAPIProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp S

/-- Compact downstream API theorem including route receipts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteAPIProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerCompactAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceipts S⟩

/-- Compact downstream API proposition including the subset-chain certificate. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSubsetAPIProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteAPIProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp S

/-- Compact downstream API theorem including the subset-chain certificate. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSubsetAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSubsetAPIProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChain S⟩

/-- Full compact downstream API proposition for public consumer users. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPIProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSubsetAPIProp S ∧
      (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S ∧
        euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp S) ∧
      (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S ∧
        euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp S)

/-- Full compact downstream API theorem for public consumer users. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPIProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSubsetAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint_complete S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint_withSubsetChain S⟩

end

end MathlibAnalytic
end MGAP4D
