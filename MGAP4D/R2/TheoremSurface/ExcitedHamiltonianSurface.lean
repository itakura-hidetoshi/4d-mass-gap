import MGAP4D.R2.TheoremSurface.RestrictionSurface
import MGAP4D.R2.Concrete.ExcitedHamiltonianStatus

namespace MGAP4D
namespace R2
namespace TheoremSurface

structure ExcitedHamiltonianSurface where
  restrictionSurfaceReady : Prop
  excitedHamiltonianStatusReady : Prop
  operatorSurface : Prop
  nonnegativeSurface : Prop
  formLinkSurface : Prop

def ExcitedHamiltonianSurface.ready (S : ExcitedHamiltonianSurface) : Prop :=
  S.restrictionSurfaceReady ∧ S.excitedHamiltonianStatusReady ∧ S.operatorSurface ∧
  S.nonnegativeSurface ∧ S.formLinkSurface

theorem excited_hamiltonian_surface_pack
    (S : ExcitedHamiltonianSurface) :
    S.ready ↔ S.restrictionSurfaceReady ∧ S.excitedHamiltonianStatusReady ∧ S.operatorSurface ∧
      S.nonnegativeSurface ∧ S.formLinkSurface := by
  rfl

end TheoremSurface
end R2
end MGAP4D
