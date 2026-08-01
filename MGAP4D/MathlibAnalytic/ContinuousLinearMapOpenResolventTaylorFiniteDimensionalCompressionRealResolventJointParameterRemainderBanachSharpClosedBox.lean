import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachSharpCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachClosedBox
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

/-- Quantitative arbitrary-joint-net closed-box data for sharp complete
remainder-tail certificates after finite-dimensional compression. -/
structure JointRemainderClosedBoxSharpCertificateData
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} (directions : ℕ) where
  D : JointRemainderClosedBoxData (α := α) (β := β) (E := E) (V := V)
    (l := l) (gap := gap) (F := F) (n := n) directions
  q : ℝ
  M : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  hM : 0 < M
  hlimitPerturb : ∀ p, D.box.Contains p → ∀ z ∈ D.Z, ∀ k : Fin 1,
    ‖closedBoxJointRemainderLimitBaseFamily
        D.J D.Q D.S.limitResolvent p z k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions D.H0 D.ds D.h‖ ≤ q
  hlimitEnd : ∀ p, D.box.Contains p → ∀ z ∈ D.Z, ∀ k : Fin 1,
    ‖closedBoxJointRemainderLimitEndpointFamily
        D.J D.Q directions D.S.limitResolvent p z D.H0 D.ds D.h k‖ ≤ M

/-- The exact carrier base order used on the complete closed box. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.carrierOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderCarrierSharpOrder C.q C.M (epsilon / 2)

/-- Arbitrary joint-net eventual smallness of the complete carrier tail at one
explicit natural-number base order, uniformly on the closed box. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_carrier_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.carrierOrder epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.carrier_tendsto
    (C.carrierOrder epsilon) tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with b hb
  intro p hp z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (C.carrierOrder epsilon) 0 tailOrder directions
      (C.D.H b) C.D.ds C.D.h
      (closedBoxJointRemainderApproxBaseFamily
        C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
      (closedBoxJointRemainderApproxEndpointFamily
        C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
        p z (C.D.H b) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (C.carrierOrder epsilon) 0 tailOrder directions C.D.H0 C.D.ds C.D.h
      (closedBoxJointRemainderLimitBaseFamily
        C.D.J C.D.Q C.D.S.limitResolvent p z)
      (closedBoxJointRemainderLimitEndpointFamily
        C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    simpa [A0, JointRemainderClosedBoxSharpCertificateData.carrierOrder] using
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_at_sharpOrder
        0 tailOrder directions C.D.H0 C.D.ds C.D.h
        (closedBoxJointRemainderLimitBaseFamily
          C.D.J C.D.Q C.D.S.limitResolvent p z)
        (closedBoxJointRemainderLimitEndpointFamily
          C.D.J C.D.Q directions C.D.S.limitResolvent p z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb p hp z hz k)
        (fun k => C.hlimitEnd p hp z hz k) hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using hb p hp z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The universally valid closed-box response order. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.responseOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderResponseSafeOrder φ C.q C.M (epsilon / 2)

/-- Arbitrary joint-net eventual smallness of every Banach-valued response
tail at one explicit natural-number base order. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_response_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ (C.responseOrder φ epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.response_tendsto φ
    (C.responseOrder φ epsilon) tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with b hb
  intro p hp z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ (C.responseOrder φ epsilon) 0 tailOrder directions
      (C.D.H b) C.D.ds C.D.h
      (closedBoxJointRemainderApproxBaseFamily
        C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
      (closedBoxJointRemainderApproxEndpointFamily
        C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
        p z (C.D.H b) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ (C.responseOrder φ epsilon) 0 tailOrder directions
      C.D.H0 C.D.ds C.D.h
      (closedBoxJointRemainderLimitBaseFamily
        C.D.J C.D.Q C.D.S.limitResolvent p z)
      (closedBoxJointRemainderLimitEndpointFamily
        C.D.J C.D.Q directions C.D.S.limitResolvent p z C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    simpa [A0, JointRemainderClosedBoxSharpCertificateData.responseOrder] using
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_at_safeOrder
        φ 0 tailOrder directions C.D.H0 C.D.ds C.D.h
        (closedBoxJointRemainderLimitBaseFamily
          C.D.J C.D.Q C.D.S.limitResolvent p z)
        (closedBoxJointRemainderLimitEndpointFamily
          C.D.J C.D.Q directions C.D.S.limitResolvent p z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb p hp z hz k)
        (fun k => C.hlimitEnd p hp z hz k) hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using hb p hp z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- The universally valid closed-box trace order. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.traceOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (epsilon : ℝ) : ℕ :=
  C.responseOrder (continuousLinearMapTrace (V := V)) epsilon

/-- Arbitrary joint-net eventual smallness of basis-independent trace tails. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_trace_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.traceOrder epsilon) 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    C.eventually_response_norm_lt (continuousLinearMapTrace (V := V))
      tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
