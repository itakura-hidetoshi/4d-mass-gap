import MGAP4D.R5.TheoremSurface.SpectrumSetSurface
import MGAP4D.R5.Concrete.InfimumStatus

namespace MGAP4D
namespace R5
namespace TheoremSurface

structure InfimumSurface where
  spectrumSetReady : Prop
  infimumStatusReady : Prop
  bottomSurface : Prop
  membershipSurface : Prop
  comparisonSurface : Prop

def InfimumSurface.ready (S : InfimumSurface) : Prop :=
  S.spectrumSetReady ∧ S.infimumStatusReady ∧ S.bottomSurface ∧
  S.membershipSurface ∧ S.comparisonSurface

theorem infimum_surface_pack
    (S : InfimumSurface) :
    S.ready ↔ S.spectrumSetReady ∧ S.infimumStatusReady ∧ S.bottomSurface ∧
      S.membershipSurface ∧ S.comparisonSurface := by
  rfl

end TheoremSurface
end R5
end MGAP4D
