import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiBlockToleranceCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductToleranceClosedBox
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

variable {α γ E V ι κ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Arbitrary-joint-net closed-box block-tolerance master order. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
    φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
    (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
    (epsilonTrace / 2)

/-- Closed-box carrier order lies below the block master. -/
theorem JointRemainderClosedBoxSharpCertificateData.carrierOrder_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.carrierOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Closed-box exact block-bundle response order lies below the block master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_blockBundle_le_toleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ blockOf) epsilonBundle ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Every closed-box block response order lies below the common block master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (b : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf b)
        (epsilonBlock b) ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
      φ blockOf b C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun c => epsilonBlock c / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Every original coordinate response order lies below the closed-box block
master. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
      φ blockOf i C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun j => epsilonCoordinate j / 2)
      (epsilonTrace / 2)

/-- Closed-box trace order lies below the block master. -/
theorem JointRemainderClosedBoxSharpCertificateData.traceOrder_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderClosedBoxSharpCertificateData.traceOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- The closed-box block master eventually controls all five channels over an
arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
      epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ blockOf)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBundle ∧
      (∀ c, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf c)
          N 0 tailOrder directions (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilonBlock c) ∧
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
  let N := C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
    epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace
  have hc := C.eventually_carrier_norm_lt_of_order_le N tailOrder epsilonCarrier
    (C.carrierOrder_le_dependentPiBlockToleranceMaster
      φ blockOf epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hCarrier
  have hbu := C.eventually_response_norm_lt_of_order_le
    (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ blockOf)
    N tailOrder epsilonBundle
    (C.responseOrder_blockBundle_le_toleranceMaster
      φ blockOf epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hBundle
  have hbs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    (fun c => continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf c)
    N tailOrder epsilonBlock
    (fun c => C.responseOrder_block_le_dependentPiBlockToleranceMaster
      φ blockOf c epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hBlock
  have hcs := C.eventually_dependentPi_response_norm_lt_of_toleranceOrders
    φ N tailOrder epsilonCoordinate
    (fun i => C.responseOrder_coord_le_dependentPiBlockToleranceMaster
      φ blockOf i epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hCoordinate
  have ht := C.eventually_trace_norm_lt_of_order_le N tailOrder epsilonTrace
    (C.traceOrder_le_dependentPiBlockToleranceMaster
      φ blockOf epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
    hTrace
  filter_upwards [hc, hbu, hbs, hcs, ht] with b hca hba hbsa hcsa hta
  intro p hpbox z hz
  exact ⟨hca p hpbox z hz, hba p hpbox z hz,
    (fun c => hbsa c p hpbox z hz),
    (fun i => hcsa i p hpbox z hz), hta p hpbox z hz⟩

/-- Under non-stricter block tolerances, the closed-box block master is exactly
the previous closed-box vector-tolerance master. -/
theorem JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter γ} {directions : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := γ) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) (hBlock : ∀ b, 0 < epsilonBlock b)
    (hRelax : ∀ b, epsilonProduct ≤ epsilonBlock b) :
    C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonProduct epsilonBlock epsilonCoordinate epsilonTrace =
      C.dependentPiProductToleranceMasterOrder φ epsilonCarrier
        epsilonProduct epsilonCoordinate epsilonTrace := by
  have hp : 0 < epsilonProduct / 2 := half_pos hProduct
  have hb : ∀ b, 0 < epsilonBlock b / 2 := fun b => half_pos (hBlock b)
  have hr : ∀ b, epsilonProduct / 2 ≤ epsilonBlock b / 2 := by
    intro b
    linarith [hRelax b]
  simpa [JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder,
    JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
      φ blockOf (fun b => epsilonBlock b / 2)
      (fun i => epsilonCoordinate i / 2) C.hq0 C.hq1 C.hM hp hb hr

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D