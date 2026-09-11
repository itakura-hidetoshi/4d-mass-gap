import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductToleranceCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductEncodingCompact
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

/-- The compact vector-tolerance master order for a dependent finite response
family.  Each tolerance is halved exactly as in the existing compact sharp
certificate interface. -/
noncomputable def JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
    φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
    (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The compact carrier order lies below the vector-tolerance master. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.carrierOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The compact encoded Pi-product response order lies below the common
vector-tolerance master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_dependentPiProduct_le_toleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        epsilonProduct ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every compact coordinate response order, with its own tolerance, lies below
the common vector-tolerance master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
      φ i C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun j => epsilonCoordinate j / 2) (epsilonTrace / 2)

/-- The compact trace order lies below the vector-tolerance master. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_dependentPiProductToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiProductToleranceMasterOrder
        φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
      φ C.q C.M (epsilonCarrier / 2) (epsilonProduct / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Differently typed compact response conditions with coordinate-dependent
tolerances can be intersected into one eventual statement. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (baseOrder tailOrder : ℕ) (epsilon : ι → ℝ)
    (horders : ∀ i, C.responseOrder (φ i) (epsilon i) ≤ baseOrder)
    (hepsilon : ∀ i, 0 < epsilon i) :
    ∀ᶠ a in l, ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon i := by
  have hi : ∀ i, ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon i :=
    fun i => C.eventually_response_norm_lt_of_order_le
      (φ i) baseOrder tailOrder (epsilon i) (horders i) (hepsilon i)
  change {a | ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon i} ∈ l
  rw [show {a | ∀ i, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon i} =
      ⋂ i, {a | ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) baseOrder taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilon i} by ext a; simp]
  exact Filter.iInter_mem.2 hi

/-- The compact vector-tolerance master eventually controls carrier, encoded
Pi-product, every differently typed coordinate, and trace at their respective
tolerances. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
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
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiProductObservable φ)
          N taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonProduct ∧
      (∀ i,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) N taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilonCoordinate i) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V N taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonTrace := by
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
  filter_upwards [hcarrier, hproduct, hcoords, htrace] with a hc hp hcs ht
  intro lambda hlambda z hz
  exact ⟨hc lambda hlambda z hz,
    hp lambda hlambda z hz,
    (fun i => hcs i lambda hlambda z hz),
    ht lambda hlambda z hz⟩

/-- Compact finite-subfamily restriction cannot increase the vector-tolerance
master order. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
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
  simpa [JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_subfamily_le
      φ s (fun i => epsilonCoordinate i / 2)
      C.hq0 C.hq1 C.hM hhalf

/-- Compact homogeneous vector-tolerance master order is invariant when
observables and coordinate tolerances are reindexed together. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions responseCount : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
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
  simpa [JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_reindex_eq
      φ (fun i => epsilonCoordinate i / 2) e
      C.hq0 C.hq1 C.hM hhalf

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
