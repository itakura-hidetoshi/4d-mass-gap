import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachSharpCertificateCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachCompact
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

/-- Quantitative compact data for a sharp complete remainder-tail certificate.
Only compressed finite-dimensional resolvents occur in the added bounds. -/
structure JointRemainderCompactSharpCertificateData
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (taylorOrder directions : ℕ) where
  D : JointRemainderCompactData (α := α) (E := E) (V := V)
    (l := l) (gap := gap) (F := F) taylorOrder directions
  q : ℝ
  M : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  hM : 0 < M
  hlimitPerturb : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
    ‖compressedJointRemainderBaseResolventFamily
        D.J D.Q taylorOrder D.S.limitResolvent lambda z k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions D.H0 D.ds D.h‖ ≤ q
  hlimitEnd : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
    ‖compressedJointRemainderEndpointResolventFamily
        D.J D.Q taylorOrder directions D.S.limitResolvent lambda z
        D.H0 D.ds D.h k‖ ≤ M

/-- The exact carrier order used for compact approximation certificates.  The
half tolerance leaves room for approximation-to-limit transfer. -/
noncomputable def JointRemainderCompactSharpCertificateData.carrierOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderCarrierSharpOrder C.q C.M (epsilon / 2)

/-- Compact-uniform eventual smallness of the complete carrier remainder tail
at one explicit natural-number base order. -/
theorem JointRemainderCompactSharpCertificateData.eventually_carrier_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.carrierOrder epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.carrier_tendsto
    (C.carrierOrder epsilon) tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with a ha
  intro lambda hlambda z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (C.carrierOrder epsilon) taylorOrder tailOrder directions
      (C.D.H a) C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder (F a) lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions (F a) lambda z
        (C.D.H a) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (C.carrierOrder epsilon) taylorOrder tailOrder directions
      C.D.H0 C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
        C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    simpa [A0, JointRemainderCompactSharpCertificateData.carrierOrder] using
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_at_sharpOrder
        taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
        (compressedJointRemainderBaseResolventFamily
          C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
        (compressedJointRemainderEndpointResolventFamily
          C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb k lambda hlambda z hz)
        (fun k => C.hlimitEnd k lambda hlambda z hz) hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using ha lambda hlambda z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The explicit universally valid compact response order. -/
noncomputable def JointRemainderCompactSharpCertificateData.responseOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderResponseSafeOrder φ C.q C.M (epsilon / 2)

/-- Compact-uniform eventual smallness after every Banach-valued continuous
linear observation, at an explicit natural-number base order. -/
theorem JointRemainderCompactSharpCertificateData.eventually_response_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ (C.responseOrder φ epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.response_tendsto φ
    (C.responseOrder φ epsilon) tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with a ha
  intro lambda hlambda z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ (C.responseOrder φ epsilon) taylorOrder tailOrder directions
      (C.D.H a) C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder (F a) lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions (F a) lambda z
        (C.D.H a) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ (C.responseOrder φ epsilon) taylorOrder tailOrder directions
      C.D.H0 C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
        C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    simpa [A0, JointRemainderCompactSharpCertificateData.responseOrder] using
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_at_safeOrder
        φ taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
        (compressedJointRemainderBaseResolventFamily
          C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
        (compressedJointRemainderEndpointResolventFamily
          C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb k lambda hlambda z hz)
        (fun k => C.hlimitEnd k lambda hlambda z hz) hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using ha lambda hlambda z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- The explicit universally valid compact trace order. -/
noncomputable def JointRemainderCompactSharpCertificateData.traceOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (epsilon : ℝ) : ℕ :=
  C.responseOrder (continuousLinearMapTrace (V := V)) epsilon

/-- Compact-uniform eventual smallness of basis-independent trace tails. -/
theorem JointRemainderCompactSharpCertificateData.eventually_trace_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.traceOrder epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    C.eventually_response_norm_lt (continuousLinearMapTrace (V := V))
      tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
