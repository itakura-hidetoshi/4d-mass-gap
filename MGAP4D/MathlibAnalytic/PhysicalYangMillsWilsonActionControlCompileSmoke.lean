import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionControl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile gate for the renormalized Wilson-action control route. -/
noncomputable def compact_wilson_weak_limit_of_action_control_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_actionControl
    E Phi scale offset D M

end

end MathlibAnalytic
end MGAP4D
