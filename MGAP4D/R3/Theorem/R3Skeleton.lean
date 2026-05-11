import MGAP4D.R3.Concrete.R3ProofObligationMap

namespace MGAP4D
namespace R3
namespace Theorem

structure R3Skeleton where
  obligationMapReady : Prop
  shiftedTheoremTarget : Prop
  nonnegativeTheoremTarget : Prop
  zeroFormTheoremTarget : Prop
  sqrtRouteTheoremTarget : Prop
  bridgeTheoremTarget : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def R3Skeleton.ready (S : R3Skeleton) : Prop :=
  S.obligationMapReady ∧ S.shiftedTheoremTarget ∧ S.nonnegativeTheoremTarget ∧
  S.zeroFormTheoremTarget ∧ S.sqrtRouteTheoremTarget ∧ S.bridgeTheoremTarget ∧
  S.mathlibRequestLinked ∧ S.statusCompatibilityHeld ∧ S.publicBoundaryHeld

theorem r3_skeleton_pack
    (S : R3Skeleton) :
    S.ready ↔ S.obligationMapReady ∧ S.shiftedTheoremTarget ∧ S.nonnegativeTheoremTarget ∧
      S.zeroFormTheoremTarget ∧ S.sqrtRouteTheoremTarget ∧ S.bridgeTheoremTarget ∧
      S.mathlibRequestLinked ∧ S.statusCompatibilityHeld ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
