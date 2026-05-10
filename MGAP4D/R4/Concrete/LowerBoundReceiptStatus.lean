import MGAP4D.R2.Concrete

namespace MGAP4D
namespace R4
namespace Concrete

structure LowerBoundReceiptStatus where
  r2ExcitedHamiltonianReady : Prop
  decompositionLedgerRecorded : Prop
  rationalConstantRecorded : Prop
  lowerBoundTargetRecorded : Prop
  analyticEstimatesDeferred : Prop

def LowerBoundReceiptStatus.ready (S : LowerBoundReceiptStatus) : Prop :=
  S.r2ExcitedHamiltonianReady ∧ S.decompositionLedgerRecorded ∧
  S.rationalConstantRecorded ∧ S.lowerBoundTargetRecorded ∧ S.analyticEstimatesDeferred

theorem lower_bound_receipt_status_pack
    (S : LowerBoundReceiptStatus) :
    S.ready ↔ S.r2ExcitedHamiltonianReady ∧ S.decompositionLedgerRecorded ∧
      S.rationalConstantRecorded ∧ S.lowerBoundTargetRecorded ∧ S.analyticEstimatesDeferred := by
  rfl

end Concrete
end R4
end MGAP4D
