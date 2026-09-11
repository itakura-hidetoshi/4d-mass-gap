import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyToleranceCompact
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

variable {α γ E V ι τ β : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype τ] [Fintype β]
variable [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Arbitrary-joint-net closed-box finite-rooted-hierarchy master order. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
    φ Htree C.q C.M (epsilonCarrier / 2)
    (fun t => epsilonBundle t / 2)
    (fun t b => epsilonBlock t b / 2)
    (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Closed-box carrier order lies below the rooted hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
        φ Htree epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.carrierOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree C.q C.M (epsilonCarrier / 2)
      (fun t => epsilonBundle t / 2) (fun t b => epsilonBlock t b / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box node-bundle order lies below the rooted hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_nodeBundle_le_finiteRootedHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ (Htree.blockOf t)) (epsilonBundle t) ≤
      C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
        φ Htree epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_nodeBundle_le_finiteRootedHierarchyToleranceMaster
      φ Htree t C.q C.M (epsilonCarrier / 2)
      (fun s => epsilonBundle s / 2) (fun s b => epsilonBlock s b / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box node-block order lies below the rooted hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_nodeBlock_le_finiteRootedHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (b : β) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (Htree.blockOf t) b) (epsilonBlock t b) ≤
      C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
        φ Htree epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_nodeBlock_le_finiteRootedHierarchyToleranceMaster
      φ Htree t b C.q C.M (epsilonCarrier / 2)
      (fun s => epsilonBundle s / 2) (fun s c => epsilonBlock s c / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- Every closed-box coordinate order lies below the rooted hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (i : ι) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
        φ Htree epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree i C.q C.M (epsilonCarrier / 2)
      (fun t => epsilonBundle t / 2) (fun t b => epsilonBlock t b / 2)
      (fun j => epsilonCoordinate j / 2) (epsilonTrace / 2)

/-- Closed-box trace order lies below the rooted hierarchy master. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
        φ Htree epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree C.q C.M (epsilonCarrier / 2)
      (fun t => epsilonBundle t / 2) (fun t b => epsilonBlock t b / 2)
      (fun i => epsilonCoordinate i / 2) (epsilonTrace / 2)

/-- The closed-box rooted hierarchy master controls all finite node channels
over an arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiFiniteRootedBlockHierarchyToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (tailOrder : ℕ) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
      φ Htree epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      (∀ t, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
            φ (Htree.blockOf t))
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBundle t) ∧
      (∀ t c, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ (Htree.blockOf t) c)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBlock t c) ∧
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
  let N := C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    φ Htree epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace
  have hc := C.eventually_carrier_norm_lt_of_order_le N tailOrder epsilonCarrier
    (C.carrierOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hCarrier
  have hbu := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    (fun t => continuousLinearMapJointRemainderDependentPiBlockBundleObservable
      φ (Htree.blockOf t))
    N tailOrder epsilonBundle
    (fun t => C.responseOrder_nodeBundle_le_finiteRootedHierarchyToleranceMaster
      φ Htree t epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hBundle
  have hbs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    (fun p : τ × β => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ (Htree.blockOf p.1) p.2)
    N tailOrder (fun p : τ × β => epsilonBlock p.1 p.2)
    (fun p => C.responseOrder_nodeBlock_le_finiteRootedHierarchyToleranceMaster
      φ Htree p.1 p.2 epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace)
    (fun p => hBlock p.1 p.2)
  have hcs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    φ N tailOrder epsilonCoordinate
    (fun i => C.responseOrder_coord_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree i epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hCoordinate
  have ht := C.eventually_trace_norm_lt_of_order_le N tailOrder epsilonTrace
    (C.traceOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
      φ Htree epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hTrace
  filter_upwards [hc, hbu, hbs, hcs, ht] with b hca hbua hbsa hcsa hta
  intro p hp z hz
  exact ⟨hca p hp z hz,
    (fun t => hbua t p hp z hz),
    (fun t c => hbsa (t, c) p hp z hz),
    (fun i => hcsa i p hp z hz),
    hta p hp z hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
