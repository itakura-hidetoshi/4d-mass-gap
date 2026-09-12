import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachMasterCertificateCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachSharpCompact
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

/-- One compact master order simultaneously controls carrier, one arbitrary
Banach response, and basis-independent trace tails. -/
noncomputable def JointRemainderCompactSharpCertificateData.masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderMasterSafeOrder φ C.q C.M (epsilon / 2)

/-- The compact carrier order is below the compact master order. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.carrierOrder epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderCarrierSharpOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- The compact response order is below the compact master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.responseOrder φ epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- The compact trace order is below the compact master order. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_masterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (epsilon : ℝ) :
    C.traceOrder epsilon ≤ C.masterOrder φ epsilon := by
  exact continuousLinearMapJointRemainderTraceSafeOrder_le_masterSafeOrder
    φ C.q C.M (epsilon / 2)

/-- Compact-uniform eventual carrier smallness at every base order above the
sharp compact carrier threshold. -/
theorem JointRemainderCompactSharpCertificateData.eventually_carrier_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.carrierOrder epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.carrier_tendsto baseOrder tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with a ha
  intro lambda hlambda z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder directions
      (C.D.H a) C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder (F a) lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions (F a) lambda z
        (C.D.H a) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
        C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
        baseOrder taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
        (compressedJointRemainderBaseResolventFamily
          C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
        (compressedJointRemainderEndpointResolventFamily
          C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb k lambda hlambda z hz)
        (fun k => C.hlimitEnd k lambda hlambda z hz)
        horder hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using ha lambda hlambda z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- Compact-uniform eventual response smallness at every base order above the
universally valid compact response threshold. -/
theorem JointRemainderCompactSharpCertificateData.eventually_response_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.responseOrder φ epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hconv := C.D.response_tendsto φ baseOrder tailOrder (epsilon / 2) hhalf
  filter_upwards [hconv] with a ha
  intro lambda hlambda z hz
  let A :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder taylorOrder tailOrder directions
      (C.D.H a) C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder (F a) lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions (F a) lambda z
        (C.D.H a) C.D.ds C.D.h)
  let A0 :=
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
      (compressedJointRemainderBaseResolventFamily
        C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
      (compressedJointRemainderEndpointResolventFamily
        C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
        C.D.H0 C.D.ds C.D.h)
  have hA0 : ‖A0‖ < epsilon / 2 := by
    exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        φ baseOrder taylorOrder tailOrder directions C.D.H0 C.D.ds C.D.h
        (compressedJointRemainderBaseResolventFamily
          C.D.J C.D.Q taylorOrder C.D.S.limitResolvent lambda z)
        (compressedJointRemainderEndpointResolventFamily
          C.D.J C.D.Q taylorOrder directions C.D.S.limitResolvent lambda z
          C.D.H0 C.D.ds C.D.h)
        C.q C.M (epsilon / 2) C.hq0 C.hq1 C.hM
        (fun k => C.hlimitPerturb k lambda hlambda z hz)
        (fun k => C.hlimitEnd k lambda hlambda z hz)
        horder hhalf
  have hdiff : ‖A - A0‖ < epsilon / 2 := by
    simpa [A, A0] using ha lambda hlambda z hz
  calc
    ‖A‖ = ‖(A - A0) + A0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - A0‖ + ‖A0‖ := norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hdiff hA0
    _ = epsilon := by ring

/-- Compact-uniform eventual trace smallness at every base order above the
compact trace threshold. -/
theorem JointRemainderCompactSharpCertificateData.eventually_trace_norm_lt_of_order_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horder : C.traceOrder epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    C.eventually_response_norm_lt_of_order_le
      (continuousLinearMapTrace (V := V)) baseOrder tailOrder epsilon horder hepsilon

/-- One explicit compact master certificate eventually controls carrier,
arbitrary Banach response, and trace tails simultaneously and uniformly. -/
theorem JointRemainderCompactSharpCertificateData.eventually_master_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.masterOrder φ epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ (C.masterOrder φ epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.masterOrder φ epsilon) taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hc := C.eventually_carrier_norm_lt_of_order_le
    (C.masterOrder φ epsilon) tailOrder epsilon
    (C.carrierOrder_le_masterOrder φ epsilon) hepsilon
  have hr := C.eventually_response_norm_lt_of_order_le
    φ (C.masterOrder φ epsilon) tailOrder epsilon
    (C.responseOrder_le_masterOrder φ epsilon) hepsilon
  have ht := C.eventually_trace_norm_lt_of_order_le
    (C.masterOrder φ epsilon) tailOrder epsilon
    (C.traceOrder_le_masterOrder φ epsilon) hepsilon
  filter_upwards [hc, hr, ht] with a hca hra hta
  intro lambda hlambda z hz
  exact ⟨hca lambda hlambda z hz,
    hra lambda hlambda z hz, hta lambda hlambda z hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
