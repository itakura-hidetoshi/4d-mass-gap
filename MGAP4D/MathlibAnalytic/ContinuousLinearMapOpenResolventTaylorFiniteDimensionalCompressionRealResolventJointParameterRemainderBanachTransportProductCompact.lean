import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachTransportProductCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {W X : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- On compact certificate data, contraction postcomposition cannot increase
the finite-response-family master order. -/
theorem JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder_postcompose_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) (hψ : ‖ψ‖ ≤ 1) (hepsilon : 0 < epsilon) :
    C.finiteResponseFamilyMasterOrder
        (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs) epsilon ≤
      C.finiteResponseFamilyMasterOrder φs epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  simpa [JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_postcompose_le
      ψ φs hψ C.hq0 C.hq1 C.hM hhalf

/-- The original compact finite-family master order controls every response
after contraction postcomposition, as well as carrier and trace. -/
theorem JointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_postcompose_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ)
    (hψ : ‖ψ‖ ≤ 1) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.finiteResponseFamilyMasterOrder φs epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      (∀ φ ∈ φs,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (ψ.comp φ) (C.finiteResponseFamilyMasterOrder φs epsilon)
            taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilon) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.finiteResponseFamilyMasterOrder φs epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  let N := C.finiteResponseFamilyMasterOrder φs epsilon
  have hcarrier := C.eventually_carrier_norm_lt_of_order_le
    N tailOrder epsilon
    (C.carrierOrder_le_finiteResponseFamilyMasterOrder φs epsilon) hepsilon
  have hresponses := C.eventually_response_family_norm_lt_of_orders
    (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs)
    N tailOrder epsilon
    (fun θ hθ => by
      rcases
        (continuousLinearMapJointRemainder_mem_postcomposeResponseFamily_iff
          ψ φs θ).1 hθ with ⟨φ, hφ, rfl⟩
      have hhalf : 0 < epsilon / 2 := half_pos hepsilon
      exact le_trans
        (by
          simpa [JointRemainderCompactSharpCertificateData.responseOrder] using
            continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
              ψ φ hψ C.hq0 C.hq1 C.hM hhalf)
        (C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
          φs epsilon hφ))
    hepsilon
  have htrace := C.eventually_trace_norm_lt_of_order_le
    N tailOrder epsilon
    (C.traceOrder_le_finiteResponseFamilyMasterOrder φs epsilon) hepsilon
  filter_upwards [hcarrier, hresponses, htrace] with a ha hr ht
  intro lambda hlambda z hz
  refine ⟨ha lambda hlambda z hz, ?_, ht lambda hlambda z hz⟩
  intro φ hφ
  exact hr (ψ.comp φ)
    ((continuousLinearMapJointRemainder_mem_postcomposeResponseFamily_iff
      ψ φs (ψ.comp φ)).2 ⟨φ, hφ, rfl⟩)
    lambda hlambda z hz

/-- The compact binary-product master order packages one product observable,
its two coordinate observables, the carrier, and trace. -/
noncomputable def JointRemainderCompactSharpCertificateData.binaryProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder [φ.prod θ] epsilon

/-- The compact product response order lies below the compact binary-product
master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_prod_le_binaryProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) :
    C.responseOrder (φ.prod θ) epsilon ≤
      C.binaryProductMasterOrder φ θ epsilon := by
  exact C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    [φ.prod θ] epsilon (by simp)

/-- The compact first-coordinate response order lies below the compact
binary-product master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_left_le_binaryProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.responseOrder φ epsilon ≤ C.binaryProductMasterOrder φ θ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  exact le_trans
    (by
      simpa [JointRemainderCompactSharpCertificateData.responseOrder] using
        continuousLinearMapJointRemainderResponseSafeOrder_le_prod_left
          φ θ C.hq0 C.hq1 C.hM hhalf)
    (C.responseOrder_prod_le_binaryProductMasterOrder φ θ epsilon)

/-- The compact second-coordinate response order lies below the compact
binary-product master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_right_le_binaryProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.responseOrder θ epsilon ≤ C.binaryProductMasterOrder φ θ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  exact le_trans
    (by
      simpa [JointRemainderCompactSharpCertificateData.responseOrder] using
        continuousLinearMapJointRemainderResponseSafeOrder_le_prod_right
          φ θ C.hq0 C.hq1 C.hM hhalf)
    (C.responseOrder_prod_le_binaryProductMasterOrder φ θ epsilon)

/-- The compact binary-product master order eventually controls the carrier,
product response, both coordinate responses, and trace simultaneously and
uniformly. -/
theorem JointRemainderCompactSharpCertificateData.eventually_binaryProductMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.binaryProductMasterOrder φ θ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ.prod θ) (C.binaryProductMasterOrder φ θ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ (C.binaryProductMasterOrder φ θ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          θ (C.binaryProductMasterOrder φ θ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.binaryProductMasterOrder φ θ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  let N := C.binaryProductMasterOrder φ θ epsilon
  have hfamily := C.eventually_finiteResponseFamilyMaster_norm_lt
    [φ.prod θ] tailOrder epsilon hepsilon
  have hleft := C.eventually_response_norm_lt_of_order_le
    φ N tailOrder epsilon
    (C.responseOrder_left_le_binaryProductMasterOrder φ θ epsilon hepsilon)
    hepsilon
  have hright := C.eventually_response_norm_lt_of_order_le
    θ N tailOrder epsilon
    (C.responseOrder_right_le_binaryProductMasterOrder φ θ epsilon hepsilon)
    hepsilon
  filter_upwards [hfamily, hleft, hright] with a hf hl hr
  intro lambda hlambda z hz
  exact ⟨hf lambda hlambda z hz |>.1,
    hf lambda hlambda z hz |>.2.1 (φ.prod θ) (by simp),
    hl lambda hlambda z hz,
    hr lambda hlambda z hz,
    hf lambda hlambda z hz |>.2.2⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
