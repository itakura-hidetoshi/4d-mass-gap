import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachFiniteResponseFamilyCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachMasterCompact
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

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One compact-uniform natural number simultaneously controls the carrier,
every response in a finite family, and the basis-independent trace. -/
noncomputable def JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    φs C.q C.M (epsilon / 2)

/-- The compact carrier order lies below the finite-family master order. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) :
    C.carrierOrder epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderCompactSharpCertificateData.carrierOrder,
    JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
      φs C.q C.M (epsilon / 2)

/-- Every listed compact response order lies below the finite-family master
order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    {φ : (V →L[ℝ] V) →L[ℝ] W}
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ)
    (hφ : φ ∈ φs) :
    C.responseOrder φ epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
      φs C.q C.M (epsilon / 2) hφ

/-- The compact trace order lies below the finite-family master order. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) :
    C.traceOrder epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
      φs C.q C.M (epsilon / 2)

/-- A componentwise collection of compact response-order bounds can be
intersected into one eventual statement because the response family is finite. -/
theorem JointRemainderCompactSharpCertificateData.eventually_response_family_norm_lt_of_orders
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horders : ∀ φ ∈ φs, C.responseOrder φ epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ φ ∈ φs, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  induction φs with
  | nil =>
      exact Filter.Eventually.of_forall (fun a φ hφ => by simp at hφ)
  | cons φ φs ih =>
      have hhead := C.eventually_response_norm_lt_of_order_le
        φ baseOrder tailOrder epsilon (horders φ (by simp)) hepsilon
      have htail := ih
        (fun ψ hψ => horders ψ (by simp [hψ]))
      filter_upwards [hhead, htail] with a ha hrest
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact ha
      · exact hrest ψ hψ

/-- The compact finite-family master order eventually controls carrier, every
listed Banach response, and trace simultaneously and uniformly. -/
theorem JointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
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
            φ (C.finiteResponseFamilyMasterOrder φs epsilon)
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
    φs N tailOrder epsilon
    (fun φ hφ => C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
      φs epsilon hφ) hepsilon
  have htrace := C.eventually_trace_norm_lt_of_order_le
    N tailOrder epsilon
    (C.traceOrder_le_finiteResponseFamilyMasterOrder φs epsilon) hepsilon
  filter_upwards [hcarrier, hresponses, htrace] with a ha hr ht
  intro lambda hlambda z hz
  exact ⟨ha lambda hlambda z hz,
    (fun φ hφ => hr φ hφ lambda hlambda z hz),
    ht lambda hlambda z hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
