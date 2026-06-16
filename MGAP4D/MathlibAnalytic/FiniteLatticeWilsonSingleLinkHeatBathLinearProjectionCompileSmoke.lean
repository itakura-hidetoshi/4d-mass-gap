import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathLinearProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_heat_bath_linear_projection_compile_smoke
    (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  L.singleLinkHeatBathProjectionLinearMap e

theorem finite_lattice_single_link_heat_bath_linear_projection_idempotent_compile_smoke
    (e : L.Edge) :
    (L.singleLinkHeatBathProjectionLinearMap e).comp
        (L.singleLinkHeatBathProjectionLinearMap e) =
      L.singleLinkHeatBathProjectionLinearMap e :=
  finite_lattice_singleLinkHeatBathProjectionLinearMap_idempotent L e

theorem finite_lattice_single_link_heat_bath_linear_projection_range_compile_smoke
    (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e) =
      L.offLinkFiberConstantSubmodule e :=
  finite_lattice_singleLinkHeatBathProjectionLinearMap_range L e

theorem finite_lattice_single_link_heat_bath_linear_projection_fixed_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f = f ↔
      f ∈ L.offLinkFiberConstantSubmodule e :=
  finite_lattice_singleLinkHeatBathProjectionLinearMap_fixed_iff L e f

end

end MathlibAnalytic
end MGAP4D
