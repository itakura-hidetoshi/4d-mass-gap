import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerRootSmoke
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Root-level compact API for the public consumer surface of the complete
Yang--Mills direct bounded route.

This file gives downstream imports one theorem-facing root proposition that
combines the full compact consumer API, root public route markers, endpoint
names, endpoint facts, and route receipts.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Root compact API proposition for downstream public consumer users. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootSmokeProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpointProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceiptsProp S

/-- Root compact API theorem for downstream public consumer users. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootSmoke S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerEndpoint S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRouteReceipts S⟩

/-- Complete root API package with the full consumer and subset-chain surfaces. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPI_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPIProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChainProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWithSubsetChain S⟩

end

end MathlibAnalytic
end MGAP4D
