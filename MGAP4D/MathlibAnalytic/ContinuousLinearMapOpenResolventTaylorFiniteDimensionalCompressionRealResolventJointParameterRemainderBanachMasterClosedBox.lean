import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachMasterCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachSharpClosedBox
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

/-- One closed-box master order simultaneously controls carrier, one arbitrary
Banach response, and basis-independent trace tails. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderMasterSafeOrder φ C.q C.M (epsilon / 2)

/-- The closed-box carrier order is below the master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.carrierOrder epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderCarrierSharpOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- The closed-box response order is below the master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.responseOrder φ epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- The closed-box trace order is below the master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.traceOrder epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderTraceSafeOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- Arbitrary-joint-net closed-box carrier smallness at every base order above
the sharp closed-box carrier threshold. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_carrier_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.carrierOrder epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.carrier_tendsto baseOrder tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with b hb
  intro p hp z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder 0 tailOrder directions
      (C.D.H b) C.D.ds C.D.h
      (closedBoxJointRemainderApproxBaseFamily
        C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
      (closedBoxJointRemainderApproxEndpointFamily
        C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
        p z (C.D.H b) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder 0 tailOrder directions C.D.H0 C.D.ds C.D.h
      (closedBoxJointRemainderLimitBaseFamily
        C.D.J C.D.Q C.D.S.limitResolvent p z)
      (closedBoxJointRemainderLimitEndpointFamily
        C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
        baseOrder 0 tailOrder directions C.D.H0 C.D.ds C.D.h
        (closedBoxJointRemainderLimitBaseFamily
          C.D.J C.D.Q C.D.S.limitResolvent p z)
        (closedBoxJointRemainderLimitEndpointFamily
          C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb p hp z hz k)
        (fun k => C.hlimitEnd p hp z hz k)
        horder hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using hb p hp z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- Arbitrary-joint-net closed-box response smallness at every base order above
the universally valid response threshold. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_response_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.responseOrder φ epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.response_tendsto φ baseOrder tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with b hb
  intro p hp z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder 0 tailOrder directions
      (C.D.H b) C.D.ds C.D.h
      (closedBoxJointRemainderApproxBaseFamily
        C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
      (closedBoxJointRemainderApproxEndpointFamily
        C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
        p z (C.D.H b) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder 0 tailOrder directions C.D.H0 C.D.ds C.D.h
      (closedBoxJointRemainderLimitBaseFamily
        C.D.J C.D.Q C.D.S.limitResolvent p z)
      (closedBoxJointRemainderLimitEndpointFamily
        C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        φ baseOrder 0 tailOrder directions C.D.H0 C.D.ds C.D.h
        (closedBoxJointRemainderLimitBaseFamily
          C.D.J C.D.Q C.D.S.limitResolvent p z)
        (closedBoxJointRemainderLimitEndpointFamily
          C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb p hp z hz k)
        (fun k => C.hlimitEnd p hp z hz k)
        horder hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using hb p hp z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- Arbitrary-joint-net closed-box trace smallness at every base order above the
trace threshold. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_trace_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.traceOrder epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    C.eventually_response_norm_lt_of_order_le
      (continuousLinearMapTrace (V := V)) baseOrder tailOrder epsilon horder hepsilon

/-- One explicit closed-box master certificate eventually controls carrier,
arbitrary Banach response, and trace tails simultaneously and uniformly for an
arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_master_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.masterOrder φ epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ (C.masterOrder φ epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.masterOrder φ epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hc := C.eventually_carrier_norm_lt_of_order_le
    (C.masterOrder φ epsilon) tailOrder epsilon
    (C.carrierOrder_le_masterOrder φ epsilon) hepsilon
  have hr := C.eventually_response_norm_lt_of_order_le
    φ (C.masterOrder φ epsilon) tailOrder epsilon
    (C.responseOrder_le_masterOrder φ epsilon) hepsilon
  have ht := C.eventually_trace_norm_lt_of_order_le
    (C.masterOrder φ epsilon) tailOrder epsilon
    (C.traceOrder_le_masterOrder φ epsilon) hepsilon
  filter_upwards [hc, hr, ht] with b hcb hrb htb
  intro p hp z hz
  exact ⟨hcb p hp z hz, hrb p hp z hz, htb p hp z hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
