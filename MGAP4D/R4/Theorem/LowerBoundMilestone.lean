import MGAP4D.R4.Theorem.LowerBoundSkeletonBundle
import MGAP4D.MathlibAdoptionGate.R4LowerBoundRequest

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundMilestone where
  concretePathReady : Prop
  skeletonBundleReady : Prop
  proofObligationMapReady : Prop
  r4RequestScoped : Prop
  mathlibStillDeferred : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def LowerBoundMilestone.ready (M : LowerBoundMilestone) : Prop :=
  M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
  M.r4RequestScoped ∧ M.mathlibStillDeferred ∧
  M.statusSurfacesPreserved ∧ M.publicBoundaryHeld

theorem lower_bound_milestone_pack
    (M : LowerBoundMilestone) :
    M.ready ↔ M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
      M.r4RequestScoped ∧ M.mathlibStillDeferred ∧
      M.statusSurfacesPreserved ∧ M.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
