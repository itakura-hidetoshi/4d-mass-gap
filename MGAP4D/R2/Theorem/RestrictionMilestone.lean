import MGAP4D.R2.Theorem.RestrictionSkeletonBundle
import MGAP4D.MathlibAdoptionGate.R2RestrictionRequest

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionMilestone where
  concretePathReady : Prop
  skeletonBundleReady : Prop
  proofObligationMapReady : Prop
  r2RestrictionRequestScoped : Prop
  mathlibStillDeferred : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def RestrictionMilestone.ready (M : RestrictionMilestone) : Prop :=
  M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
  M.r2RestrictionRequestScoped ∧ M.mathlibStillDeferred ∧
  M.statusSurfacesPreserved ∧ M.publicBoundaryHeld

theorem restriction_milestone_pack
    (M : RestrictionMilestone) :
    M.ready ↔ M.concretePathReady ∧ M.skeletonBundleReady ∧ M.proofObligationMapReady ∧
      M.r2RestrictionRequestScoped ∧ M.mathlibStillDeferred ∧
      M.statusSurfacesPreserved ∧ M.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
