import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapRouteCompileSmoke

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def routeSmokeFinal : Prop := continuumMassGapRoutePublicReleaseCompileSmoke

theorem routeSmokeFinal_holds : routeSmokeFinal :=
  continuumMassGapRoutePublicReleaseCompileSmoke_holds

end

end MathlibAnalytic
end MGAP4D
