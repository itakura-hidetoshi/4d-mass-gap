import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductToleranceCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductEncodingClosedBox
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

variable {α β E V ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι]

variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)]
variable [∀ i, NormedSpace ℝ (W i)]

/-- The arbitrary-joint-net closed-box vector-tolerance master order for a
dependent finite response family. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
    φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
    (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The closed-box carrier order lies below the vector-tolerance master. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.carrierOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The closed-box encoded Pi-product response order lies below the common
vector-tolerance master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_dependentPiProduct_le_toleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        epsilonProduct ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box coordinate response order, with its own tolerance, lies
below the common vector-tolerance master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
      φ i C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun j => epsilonCoordinate j / 2) (epsilonTrace / 2)

/-- The closed-box trace order lies below the vector-tolerance master. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Differently typed closed-box response conditions with coordinate-dependent
tolerances can be intersected over an arbitrary joint net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (baseOrder tailOrder : ℕ) (epsilon : ι → ℝ)
    (horders : ∀ i, C.responseOrder (φ i) (epsilon i) ≤ baseOrder)
    (hepsilon : ∀ i, 0 < epsilon i) :
    ∀ᶠ b in n, ∀ i, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon i := by
  have hi : ∀ i, ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon i :=
    fun i => C.eventually_response_norm_lt_of_order_le
      (φ i) baseOrder tailOrder (epsilon i) (horders i) (hepsilon i)
  change {b | ∀ i, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon i} ∈ n
  rw [show {b | ∀ i, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon i} =
      ⋂ i, {b | ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) baseOrder 0 tailOrder directions
            (C.D.H b) C.D.ds C.D.h
            (closedBoxJointRemainderApproxBaseFamily
              C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
            (closedBoxJointRemainderApproxEndpointFamily
              C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
              p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon i} by ext b; simp]
  exact Filter.iInter_mem.2 hi

/-- The closed-box vector-tolerance master eventually controls carrier,
encoded Pi-product, every differently typed coordinate, and trace at their
respective tolerances over an arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (tailOrder : ℕ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := C.dependentPiProductToleranceMasterOrder
      φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          N 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonProduct ∧
      (∀ i,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) N 0 tailOrder directions
            (C.D.H b) C.D.ds C.D.h
            (closedBoxJointRemainderApproxBaseFamily
              C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
            (closedBoxJointRemainderApproxEndpointFamily
              C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
              p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCoordinate i) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V N 0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonTrace := by
  dsimp
  let N := C.dependentPiProductToleranceMasterOrder
    φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
  have hcarrier := C.eventually_carrier_norm_lt_of_order_le
    N tailOrder epsilonCarrier
    (C.carrierOrder_le_dependentPiProductToleranceMaster
      φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
    hCarrier
  have hproduct := C.eventually_response_norm_lt_of_order_le
    (continuousLinearMapJointRemainderDependentPiProductObservable φ)
    N tailOrder epsilonProduct
    (C.responseOrder_dependentPiProduct_le_toleranceMaster
      φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
    hProduct
  have hcoords := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    φ N tailOrder epsilonCoordinate
    (fun i => C.responseOrder_coord_le_dependentPiProductToleranceMaster
      φ i epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
    hCoordinate
  have htrace := C.eventually_trace_norm_lt_of_order_le
    N tailOrder epsilonTrace
    (C.traceOrder_le_dependentPiProductToleranceMaster
      φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace)
    hTrace
  filter_upwards [hcarrier, hproduct, hcoords, htrace] with b hc hp hcs ht
  intro p hpbox z hz
  exact ⟨hc p hpbox z hz,
    hp p hpbox z hz,
    (fun i => hcs i p hpbox z hz),
    ht p hpbox z hz⟩

/-- Closed-box finite-subfamily restriction cannot increase the
vector-tolerance master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :
    C.dependentPiProductToleranceMasterOrder
        (fun i : {i // i ∈ s} => φ i.1)
        epsilonCarrier epsilonProduct (fun i => epsilonCoordinate i.1)
        epsilonTrace ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  have hhalf : 0 < epsilonProduct / 2 := half_pos hProduct
  simpa [JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_subfamily_le
      φ s (fun i => epsilonCoordinate i / 2)
      C.hq0 C.hq1 C.hM hhalf

/-- Closed-box homogeneous vector-tolerance master order is invariant when
observables and coordinate tolerances are reindexed together. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] U))
    (epsilonCoordinate : Fin responseCount → ℝ)
    (e : Fin responseCount ≃ Fin responseCount)
    (epsilonCarrier epsilonProduct epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :
    C.dependentPiProductToleranceMasterOrder
        (W := fun _ : Fin responseCount => U) (fun i => φ (e i))
        epsilonCarrier epsilonProduct (fun i => epsilonCoordinate (e i))
        epsilonTrace =
      C.dependentPiProductToleranceMasterOrder
        (W := fun _ : Fin responseCount => U) φ
        epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  have hhalf : 0 < epsilonProduct / 2 := half_pos hProduct
  simpa [JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_reindex_eq
      φ (fun i => epsilonCoordinate i / 2) e
      C.hq0 C.hq1 C.hM hhalf

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
