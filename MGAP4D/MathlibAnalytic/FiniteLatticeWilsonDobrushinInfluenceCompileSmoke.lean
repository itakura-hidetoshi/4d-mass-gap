import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_conditional_tv_compile_smoke
    (A B : L.Configuration) (e : L.Edge) : ℝ :=
  L.singleLinkConditionalTotalVariation A B e

theorem finite_lattice_conditional_tv_nonneg_compile_smoke
    (A B : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B e :=
  finite_lattice_singleLinkConditionalTotalVariation_nonneg L A B e

theorem finite_lattice_conditional_tv_fiber_zero_compile_smoke
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e = 0 :=
  finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    L A B e hAgree

end

end MathlibAnalytic
end MGAP4D
