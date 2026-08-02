import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyToleranceCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiBlockToleranceClosedBox
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

variable {α γ E V ι κ σ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [Fintype σ]
variable [DecidableEq κ] [DecidableEq σ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Arbitrary-joint-net closed-box two-level block hierarchy master. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
    φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
    (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
    (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Closed-box hierarchy order is the maximum of the two block masters. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_max
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
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

/-- Closed-box carrier order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.carrierOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Closed-box coarse bundle order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coarseBundle_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ coarseOf) epsilonBundle ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coarseBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Closed-box fine bundle order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_fineBundle_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ fineOf) epsilonBundle ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_fineBundle_le_hierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box coarse block order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (c : σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
        (epsilonCoarse c) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coarseBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf c C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun d => epsilonCoarse d / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box fine block order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (k : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
        (epsilonFine k) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_hierarchyToleranceMaster
      φ fineOf coarseOf k C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun j => epsilonFine j / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box coordinate order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf i C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun j => epsilonCoordinate j / 2) (epsilonTrace / 2)

/-- Closed-box trace order lies below the hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_dependentPiBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
        epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockHierarchyToleranceMaster
      φ fineOf coarseOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The closed-box hierarchy master eventually controls all seven channels over
an arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
      epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ coarseOf)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBundle ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ fineOf)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBundle ∧
      (∀ c, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCoarse c) ∧
      (∀ k, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonFine k) ∧
      (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCoordinate i) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonTrace := by
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
  filter_upwards [hc, hcb, hfb, hcbs, hfbs, hcs, ht] with b hca hcba hfba hcbsa hfbsa hcsa hta
  intro p hp z hz
  exact ⟨hca p hp z hz, hcba p hp z hz, hfba p hp z hz,
    (fun c => hcbsa c p hp z hz),
    (fun k => hfbsa k p hp z hz),
    (fun i => hcsa i p hp z hz), hta p hp z hz⟩

/-- Under inherited fine-block tolerances, the closed-box hierarchy master is
exactly the closed-box coarse block master. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines fineOf coarseOf parent)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
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
  simpa [JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_coarseMaster
      (W := W) φ fineOf coarseOf parent hrefines
      (fun i => epsilonCoordinate i / 2) C.hq0 C.hq1 C.hM hf hc hr

/-- If both block levels are no stricter than the common bundle tolerance, the
closed-box hierarchy master is exactly the closed-box product master. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : σ → ℝ)
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
  simpa [JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_productMaster
      (W := W) φ fineOf coarseOf
      (fun k => epsilonFine k / 2) (fun c => epsilonCoarse c / 2)
      (fun i => epsilonCoordinate i / 2)
      C.hq0 C.hq1 C.hM hb hf hc hfr hcr

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
