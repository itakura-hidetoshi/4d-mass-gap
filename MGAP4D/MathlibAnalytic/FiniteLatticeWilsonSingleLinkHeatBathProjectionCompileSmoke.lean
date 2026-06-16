import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {α : Type*} [Fintype α]

example (p : PMF α) :
    ∑ a : α, p a = 1 :=
  finite_pmf_sum_eq_one p

example (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 :=
  finite_pmf_sum_toReal_eq_one p

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_heat_bath_projection_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  L.singleLinkHeatBathProjection e f

theorem finite_lattice_single_link_heat_bath_projection_fiber_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.OffLinkFiberConstant e (L.singleLinkHeatBathProjection e f) :=
  finite_lattice_singleLinkHeatBathProjection_offLinkFiberConstant L e f

theorem finite_lattice_single_link_heat_bath_projection_fixes_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ)
    (hFiber : L.OffLinkFiberConstant e f) :
    L.singleLinkHeatBathProjection e f = f :=
  finite_lattice_singleLinkHeatBathProjection_fixes L e f hFiber

theorem finite_lattice_single_link_heat_bath_projection_idempotent_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) =
      L.singleLinkHeatBathProjection e f :=
  finite_lattice_singleLinkHeatBathProjection_idempotent L e f

theorem finite_lattice_single_link_heat_bath_projection_fixed_iff_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e f = f ↔
      L.OffLinkFiberConstant e f :=
  finite_lattice_singleLinkHeatBathProjection_fixed_iff L e f

end

end MathlibAnalytic
end MGAP4D
