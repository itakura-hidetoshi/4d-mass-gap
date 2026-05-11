import MGAP4D.R3.Theorem.R3SkeletonBundle
import MGAP4D.MathlibAdoptionGate.R3ZeroKernelRequest

namespace MGAP4D
namespace R3
namespace Theorem

structure R3Milestone where
  concretePathReady : Prop
  skeletonBundleReady : Prop
  proofObligationMapReady : Prop
  r3RequestScoped : Prop
  mathlibStillDeferred : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def R3Milestone.ready (M : R3Milestone) : Prop :=
  M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
  M.r3RequestScoped ∧ M.mathlibStillDeferred ∧
  M.statusSurfacesPreserved ∧ M.publicBoundaryHeld

theorem r3_milestone_pack
    (M : R3Milestone) :
    M.ready ↔ M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
      M.r3RequestScoped ∧ M.mathlibStillDeferred ∧
      M.statusSurfacesPreserved ∧ M.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
