import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_heat_bath_fluctuation_projection_compile_smoke
    (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  L.singleLinkHeatBathFluctuationLinearMap e

theorem finite_lattice_single_link_heat_bath_fluctuation_idempotent_compile_smoke
    (e : L.Edge) :
    (L.singleLinkHeatBathFluctuationLinearMap e).comp
        (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.singleLinkHeatBathFluctuationLinearMap e :=
  finite_lattice_singleLinkHeatBathFluctuationLinearMap_idempotent L e

theorem finite_lattice_single_link_heat_bath_decomposition_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f +
        L.singleLinkHeatBathFluctuationLinearMap e f = f :=
  finite_lattice_singleLinkHeatBath_projection_add_fluctuation L e f

theorem finite_lattice_single_link_heat_bath_fluctuation_ker_compile_smoke
    (e : L.Edge) :
    LinearMap.ker (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.offLinkFiberConstantSubmodule e :=
  finite_lattice_singleLinkHeatBathFluctuationLinearMap_ker L e

theorem finite_lattice_single_link_heat_bath_fluctuation_range_compile_smoke
    (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathFluctuationLinearMap e) =
      LinearMap.ker (L.singleLinkHeatBathProjectionLinearMap e) :=
  finite_lattice_singleLinkHeatBathFluctuationLinearMap_range_eq_projection_ker L e

end

end MathlibAnalytic
end MGAP4D
