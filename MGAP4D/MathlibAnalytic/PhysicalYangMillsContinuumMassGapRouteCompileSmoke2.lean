import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapRouteCompileSmoke
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def continuumMassGapRouteCompileSmoke2 : Prop :=
  continuumMassGapRoutePublicReleaseCompileSmoke

theorem continuumMassGapRouteCompileSmoke2_holds :
    continuumMassGapRouteCompileSmoke2 :=
  continuumMassGapRoutePublicReleaseCompileSmoke_holds

end

end MathlibAnalytic
end MGAP4D
