import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachMasterClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One arbitrary-joint-net closed-box natural number controls the carrier,
every response in a finite family, and the basis-independent trace. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    φs C.q C.M (epsilon / 2)

/-- The closed-box carrier order lies below the finite-family master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) :
    C.carrierOrder epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderClosedBoxSharpCertificateData.carrierOrder,
    JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
      φs C.q C.M (epsilon / 2)

/-- Every listed closed-box response order lies below the finite-family master
order. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    {φ : (V →L[ℝ] V) →L[ℝ] W}
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ)
    (hφ : φ ∈ φs) :
    C.responseOrder φ epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
      φs C.q C.M (epsilon / 2) hφ

/-- The closed-box trace order lies below the finite-family master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_finiteResponseFamilyMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) :
    C.traceOrder epsilon ≤ C.finiteResponseFamilyMasterOrder φs epsilon := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
      φs C.q C.M (epsilon / 2)

/-- A finite collection of closed-box response bounds can be intersected into
one eventual assertion over an arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_response_family_norm_lt_of_orders
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horders : ∀ φ ∈ φs, C.responseOrder φ epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ φ ∈ φs, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  induction φs with
  | nil =>
      exact Filter.Eventually.of_forall (fun b φ hφ => by simp at hφ)
  | cons φ φs ih =>
      have hhead := C.eventually_response_norm_lt_of_order_le
        φ baseOrder tailOrder epsilon (horders φ (by simp)) hepsilon
      have htail := ih
        (fun ψ hψ => horders ψ (by simp [hψ]))
      filter_upwards [hhead, htail] with b hb hrest
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hb
      · exact hrest ψ hψ

/-- The closed-box finite-family master order eventually controls carrier,
every listed Banach response, and trace simultaneously and uniformly for an
arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.finiteResponseFamilyMasterOrder φs epsilon)
          0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon ∧
      (∀ φ ∈ φs,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            φ (C.finiteResponseFamilyMasterOrder φs epsilon)
            0 tailOrder directions
            (C.D.H b) C.D.ds C.D.h
            (closedBoxJointRemainderApproxBaseFamily
              C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
            (closedBoxJointRemainderApproxEndpointFamily
              C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
              p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.finiteResponseFamilyMasterOrder φs epsilon)
          0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
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
  filter_upwards [hcarrier, hresponses, htrace] with b hb hr ht
  intro p hp z hz
  exact ⟨hb p hp z hz,
    (fun φ hφ => hr φ hφ p hp z hz),
    ht p hp z hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
