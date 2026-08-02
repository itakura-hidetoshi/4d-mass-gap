import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyToleranceCertificateCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiBlockToleranceCompact
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

variable {α E V ι κ λ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [Fintype λ]
variable [DecidableEq κ] [DecidableEq λ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Compact two-level block hierarchy master with exact halving of all strict
tolerances. -/
noncomputable def JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
    φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
    (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
    (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Compact hierarchy order is the maximum of the coarse and fine compact
block masters. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_max
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace =
      max
        (C.dependentPiBlockToleranceMasterOrder φ coarseOf epsilonCarrier
          epsilonBundle epsilonCoarse epsilonCoordinate epsilonTrace)
        (C.dependentPiBlockToleranceMasterOrder φ fineOf epsilonCarrier
          epsilonBundle epsilonFine epsilonCoordinate epsilonTrace) := by
  rfl

/-- Compact carrier order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.carrierOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Compact coarse bundle order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coarseBundle_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ coarseOf) epsilonBundle ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coarseBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Compact fine bundle order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_fineBundle_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ fineOf) epsilonBundle ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_fineBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every compact coarse block order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (c : λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
        (epsilonCoarse c) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coarseBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf c C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun d => epsilonCoarse d / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every compact fine block order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (k : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
        (epsilonFine k) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf k C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun j => epsilonFine j / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every compact coordinate order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf i C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun j => epsilonCoordinate j / 2) (epsilonTrace / 2)

/-- Compact trace order lies below the hierarchy master. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The compact hierarchy master eventually controls both bundles, both block
families, every original coordinate, carrier, and trace. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
      epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ coarseOf)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonBundle ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ fineOf)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonBundle ∧
      (∀ c, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonCoarse c) ∧
      (∀ k, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonFine k) ∧
      (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonCoordinate i) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonTrace := by
  dsimp
  let N := C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
    epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace
  have hc := C.eventually_carrier_norm_lt_of_order_le N tailOrder epsilonCarrier
    (C.carrierOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hCarrier
  have hcb := C.eventually_response_norm_lt_of_order_le
    (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ coarseOf)
    N tailOrder epsilonBundle
    (C.responseOrder_coarseBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hBundle
  have hfb := C.eventually_response_norm_lt_of_order_le
    (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ fineOf)
    N tailOrder epsilonBundle
    (C.responseOrder_fineBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hBundle
  have hcbs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    (fun c => continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
    N tailOrder epsilonCoarse
    (fun c => C.responseOrder_coarseBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf c epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hCoarse
  have hfbs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    (fun k => continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
    N tailOrder epsilonFine
    (fun k => C.responseOrder_fineBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf k epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hFine
  have hcs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    φ N tailOrder epsilonCoordinate
    (fun i => C.responseOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf i epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hCoordinate
  have ht := C.eventually_trace_norm_lt_of_order_le N tailOrder epsilonTrace
    (C.traceOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace) hTrace
  filter_upwards [hc, hcb, hfb, hcbs, hfbs, hcs, ht] with a hca hcba hfba hcbsa hfbsa hcsa hta
  intro lambda hlambda z hz
  exact ⟨hca lambda hlambda z hz, hcba lambda hlambda z hz,
    hfba lambda hlambda z hz,
    (fun c => hcbsa c lambda hlambda z hz),
    (fun k => hfbsa k lambda hlambda z hz),
    (fun i => hcsa i lambda hlambda z hz), hta lambda hlambda z hz⟩

/-- Under inherited fine-block tolerances, the compact hierarchy master is
exactly the compact coarse block master. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (parent : κ → λ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines fineOf coarseOf parent)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :
    C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace =
      C.dependentPiBlockToleranceMasterOrder φ coarseOf epsilonCarrier
        epsilonBundle epsilonCoarse epsilonCoordinate epsilonTrace := by
  have hf : ∀ k, 0 < epsilonFine k / 2 := fun k => half_pos (hFine k)
  have hc : ∀ c, 0 < epsilonCoarse c / 2 := fun c => half_pos (hCoarse c)
  have hr : ∀ k, epsilonCoarse (parent k) / 2 ≤ epsilonFine k / 2 := by
    intro k
    linarith [hRelax k]
  simpa [JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_coarseMaster
      (W := W) φ fineOf coarseOf parent hrefines
      (fun i => epsilonCoordinate i / 2) C.hq0 C.hq1 C.hM hf hc hr

/-- If both block levels are no stricter than the common bundle tolerance, the
compact hierarchy master is exactly the compact product master. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hFineRelax : ∀ k, epsilonBundle ≤ epsilonFine k)
    (hCoarseRelax : ∀ c, epsilonBundle ≤ epsilonCoarse c) :
    C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace =
      C.dependentPiProductToleranceMasterOrder φ epsilonCarrier
        epsilonBundle epsilonCoordinate epsilonTrace := by
  have hb : 0 < epsilonBundle / 2 := half_pos hBundle
  have hf : ∀ k, 0 < epsilonFine k / 2 := fun k => half_pos (hFine k)
  have hc : ∀ c, 0 < epsilonCoarse c / 2 := fun c => half_pos (hCoarse c)
  have hfr : ∀ k, epsilonBundle / 2 ≤ epsilonFine k / 2 := by
    intro k
    linarith [hFineRelax k]
  have hcr : ∀ c, epsilonBundle / 2 ≤ epsilonCoarse c / 2 := by
    intro c
    linarith [hCoarseRelax c]
  simpa [JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_productMaster
      (W := W) φ fineOf coarseOf
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2)
      C.hq0 C.hq1 C.hM hb hf hc hfr hcr

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
