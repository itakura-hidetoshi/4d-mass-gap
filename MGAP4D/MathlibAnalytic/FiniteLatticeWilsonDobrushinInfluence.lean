import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite total-variation distance between two exact single-link Wilson
conditional laws. -/
def FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) : ℝ := by
  classical
  exact (2 : ℝ)⁻¹ *
    ∑ g : L.Gauge,
      |(L.singleLinkConditionalPMF A e g).toReal -
        (L.singleLinkConditionalPMF B e g).toReal|

/-- Conditional total variation is nonnegative. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun g _hg => abs_nonneg _)

/-- The conditional total variation vanishes when the two configurations agree
outside the link being resampled. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalTotalVariation A B e = 0 := by
  classical
  have hPMF :
      L.singleLinkConditionalPMF A e =
        L.singleLinkConditionalPMF B e :=
    finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B e hAgree
  simp [FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation, hPMF]

end

end MathlibAnalytic
end MGAP4D
