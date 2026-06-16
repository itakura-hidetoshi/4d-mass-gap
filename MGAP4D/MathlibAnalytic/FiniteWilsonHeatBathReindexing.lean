import MGAP4D.MathlibAnalytic.FiniteWilsonLinkExchange
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Detailed balance reindexes the finite configuration--gauge update sum by
exchanging the old and newly sampled value of the selected link. -/
theorem finite_lattice_singleLinkHeatBath_reversible_product_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.gibbsProbabilityReal x.1 *
        (L.singleLinkConditionalPMF x.1 e x.2).toReal *
        f (L.replaceLink x.1 e x.2) * g x.1) =
      ∑ x : L.Configuration × L.Gauge,
        L.gibbsProbabilityReal x.1 *
          (L.singleLinkConditionalPMF x.1 e x.2).toReal *
          f x.1 * g (L.replaceLink x.1 e x.2) := by
  classical
  refine Fintype.sum_equiv (L.singleLinkUpdateSwapEquiv e) _ _ ?_
  rintro ⟨A, h⟩
  change L.gibbsProbabilityReal A *
      (L.singleLinkConditionalPMF A e h).toReal *
      f (L.replaceLink A e h) * g A =
    L.gibbsProbabilityReal (L.replaceLink A e h) *
      (L.singleLinkConditionalPMF
        (L.replaceLink A e h) e (A e)).toReal *
      f (L.replaceLink A e h) *
      g (L.replaceLink (L.replaceLink A e h) e (A e))
  rw [finite_lattice_singleLinkHeatBath_detailedBalance_real]
  simp

end

end MathlibAnalytic
end MGAP4D
