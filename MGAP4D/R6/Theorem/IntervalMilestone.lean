import MGAP4D.R6.Theorem.IntervalSkeletonBundle
import MGAP4D.MathlibAdoptionGate.R6IntervalRequest

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalMilestone where
  concretePathReady : Prop
  skeletonBundleReady : Prop
  proofObligationMapReady : Prop
  r6RequestScoped : Prop
  mathlibStillDeferred : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def IntervalMilestone.ready (M : IntervalMilestone) : Prop :=
  M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
  M.r6RequestScoped ∧ M.mathlibStillDeferred ∧
  M.statusSurfacesPreserved ∧ M.publicBoundaryHeld

theorem interval_milestone_pack
    (M : IntervalMilestone) :
    M.ready ↔ M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
      M.r6RequestScoped ∧ M.mathlibStillDeferred ∧
      M.statusSurfacesPreserved ∧ M.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
