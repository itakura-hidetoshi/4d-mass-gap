import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

example (A B : L.Configuration) (e : L.Edge) : Prop :=
  L.AgreeOffLink A B e

theorem finite_lattice_replace_link_fiber_compile_smoke
    (A B : L.Configuration) (e : L.Edge) (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e g = L.replaceLink B e g :=
  finite_lattice_replaceLink_eq_of_agreeOffLink L A B e g hAgree

theorem finite_lattice_single_link_pmf_fiber_compile_smoke
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalPMF A e =
      L.singleLinkConditionalPMF B e :=
  finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
    L A B e hAgree

theorem finite_lattice_single_link_expectation_fiber_compile_smoke
    (f : L.Configuration → ℝ)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalExpectation f A e =
      L.singleLinkConditionalExpectation f B e :=
  finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
    L f A B e hAgree

theorem finite_lattice_single_link_variance_fiber_compile_smoke
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge) :
    L.singleLinkConditionalVariance f (L.replaceLink A e h) e =
      L.singleLinkConditionalVariance f A e :=
  finite_lattice_singleLinkConditionalVariance_replaceLink
    L f A e h

end

end MathlibAnalytic
end MGAP4D
