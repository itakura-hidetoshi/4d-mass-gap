import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceCertificateCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductToleranceCompact
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

variable {α E V ι κ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Compact block-tolerance master order, with the standard exact halving of
all strict tolerances. -/
noncomputable def JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
    φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
    (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
    (epsilonTrace / 2)

/-- Compact carrier order lies below the block master. -/
theorem JointRemainderCompactSharpCertificateData.carrierOrder_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.carrierOrder epsilonCarrier ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.carrierOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Compact exact block-bundle response order lies below the block master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_blockBundle_le_toleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ blockOf) epsilonBundle ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Every compact block response order lies below the common block master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (b : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf b)
        (epsilonBlock b) ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
      φ blockOf b C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun c => epsilonBlock c / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- Every compact original-coordinate response order lies below the block
master. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.responseOrder (φ i) (epsilonCoordinate i) ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.responseOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
      φ blockOf i C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun j => epsilonCoordinate j / 2)
      (epsilonTrace / 2)

/-- Compact trace order lies below the block master. -/
theorem JointRemainderCompactSharpCertificateData.traceOrder_le_dependentPiBlockToleranceMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    C.traceOrder epsilonTrace ≤
      C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
        epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  simpa [JointRemainderCompactSharpCertificateData.traceOrder,
    JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder] using
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
      φ blockOf C.q C.M (epsilonCarrier / 2) (epsilonBundle / 2)
      (fun b => epsilonBlock b / 2) (fun i => epsilonCoordinate i / 2)
      (epsilonTrace / 2)

/-- The compact block master eventually controls carrier, exact block bundle,
every block, every original coordinate, and trace at their own tolerances. -/
theorem JointRemainderCompactSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
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
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonCarrier ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ blockOf)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonBundle ∧
      (∀ b, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf b)
          N taylorOrder tailOrder directions (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilonBlock b) ∧
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
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf b)
    N tailOrder epsilonBlock
    (fun b => C.responseOrder_block_le_dependentPiBlockToleranceMaster
      φ blockOf b epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace)
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
  filter_upwards [hc, hbu, hbs, hcs, ht] with a hca hba hbsa hcsa hta
  intro lambda hlambda z hz
  exact ⟨hca lambda hlambda z hz, hba lambda hlambda z hz,
    (fun b => hbsa b lambda hlambda z hz),
    (fun i => hcsa i lambda hlambda z hz), hta lambda hlambda z hz⟩

/-- Under non-stricter block tolerances, the compact block master is exactly
the previous compact vector-tolerance master. -/
theorem JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
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
  simpa [JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder,
    JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder] using
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
      φ blockOf (fun b => epsilonBlock b / 2)
      (fun i => epsilonCoordinate i / 2) C.hq0 C.hq1 C.hM hp hb hr

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D