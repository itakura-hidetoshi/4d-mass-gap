import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductEncodingCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyCompact
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {α E V ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι]

variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)]
variable [∀ i, NormedSpace ℝ (W i)]

/-- The compact dependent Pi-product master order packages a finite family of
possibly different Banach codomains as one sup-norm product response. -/
noncomputable def JointRemainderCompactSharpCertificateData.dependentPiProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder
    [continuousLinearMapJointRemainderDependentPiProductObservable φ] epsilon

/-- The compact dependent product response order lies below its master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_dependentPiProduct_le_master
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilon : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ) epsilon ≤
      C.dependentPiProductMasterOrder φ epsilon := by
  exact C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    [continuousLinearMapJointRemainderDependentPiProductObservable φ]
    epsilon (by simp)

/-- Every compact dependent coordinate response order lies below the common
Pi-product master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.responseOrder (φ i) epsilon ≤
      C.dependentPiProductMasterOrder φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  exact le_trans
    (by
      simpa [JointRemainderCompactSharpCertificateData.responseOrder] using
        continuousLinearMapJointRemainderResponseSafeOrder_le_dependentPiProductObservable
          φ i C.hq0 C.hq1 C.hM hhalf)
    (C.responseOrder_dependentPiProduct_le_master φ epsilon)

/-- The compact carrier order lies below the dependent Pi-product master order. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_dependentPiProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilon : ℝ) :
    C.carrierOrder epsilon ≤ C.dependentPiProductMasterOrder φ epsilon := by
  exact C.carrierOrder_le_finiteResponseFamilyMasterOrder
    [continuousLinearMapJointRemainderDependentPiProductObservable φ] epsilon

/-- The compact trace order lies below the dependent Pi-product master order. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_dependentPiProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilon : ℝ) :
    C.traceOrder epsilon ≤ C.dependentPiProductMasterOrder φ epsilon := by
  exact C.traceOrder_le_finiteResponseFamilyMasterOrder
    [continuousLinearMapJointRemainderDependentPiProductObservable φ] epsilon

/-- Finitely many dependent compact response conditions can be intersected
into one eventual statement even though the response codomains differ. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPi_response_norm_lt_of_orders
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ)
    (horders : ∀ i, C.responseOrder (φ i) epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hi : ∀ i, ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon :=
    fun i => C.eventually_response_norm_lt_of_order_le
      (φ i) baseOrder tailOrder epsilon (horders i) hepsilon
  change {a | ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon} ∈ l
  rw [show {a | ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon} =
      ⋂ i, {a | ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) baseOrder taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilon} by ext a; simp]
  exact Filter.iInter_mem.2 hi

/-- The compact dependent Pi-product master order eventually controls the
carrier, product response, every differently typed coordinate response, and
trace simultaneously and uniformly. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPiProductMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.dependentPiProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          (C.dependentPiProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      (∀ i,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) (C.dependentPiProductMasterOrder φ epsilon)
            taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilon) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.dependentPiProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
  have hproduct := C.eventually_finiteResponseFamilyMaster_norm_lt
    [continuousLinearMapJointRemainderDependentPiProductObservable φ]
    tailOrder epsilon hepsilon
  have hcoords := C.eventually_dependentPi_response_norm_lt_of_orders
    φ (C.dependentPiProductMasterOrder φ epsilon)
    tailOrder epsilon
    (fun i => C.responseOrder_coord_le_dependentPiProductMaster
      φ i epsilon hepsilon)
    hepsilon
  filter_upwards [hproduct, hcoords] with a hp hc
  intro lambda hlambda z hz
  have hp' := hp lambda hlambda z hz
  exact ⟨hp'.1,
    hp'.2.1
      (continuousLinearMapJointRemainderDependentPiProductObservable φ) (by simp),
    (fun i => hc i lambda hlambda z hz),
    hp'.2.2⟩

/-- Compact homogeneous Pi-product master order is invariant under finite
coordinate permutations. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiProductMasterOrder_reindex_eq
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions responseCount : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] U))
    (e : Fin responseCount ≃ Fin responseCount)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.dependentPiProductMasterOrder
        (W := fun _ : Fin responseCount => U) (fun i => φ (e i)) epsilon =
      C.dependentPiProductMasterOrder
        (W := fun _ : Fin responseCount => U) φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  simpa [JointRemainderCompactSharpCertificateData.dependentPiProductMasterOrder,
    JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder] using
    continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder_reindex_eq
      φ e C.hq0 C.hq1 C.hM hhalf

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D