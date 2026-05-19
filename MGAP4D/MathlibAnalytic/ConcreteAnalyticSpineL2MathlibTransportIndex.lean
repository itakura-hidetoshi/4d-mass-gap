import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibNormAdapter
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibCoordinateTransport
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitNormTransport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Import-only index for the concrete l2 Mathlib transport lane. -/
def concreteAnalyticSpineL2MathlibTransportIndexReady : Prop :=
  concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady ∧
  concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady ∧
  concreteAnalyticSpineL2UnitNormTransportSurfaceReady

/-- The import-only transport index is ready. -/
theorem concrete_analytic_spine_l2_mathlib_transport_index_ready :
    concreteAnalyticSpineL2MathlibTransportIndexReady := by
  exact And.intro
    concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready <|
      And.intro
        concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready
        concrete_analytic_spine_l2_unit_norm_transport_surface_ready

end

end MathlibAnalytic
end MGAP4D
