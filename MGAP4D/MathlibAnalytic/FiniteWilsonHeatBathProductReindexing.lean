import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTermBalance
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact detailed balance reindexes the full finite configuration--gauge
transition sum by the involutive link exchange. -/
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
  let τ := L.singleLinkUpdateSwapEquiv e
  let lhsTerm : (L.Configuration × L.Gauge) → ℝ := fun x =>
    L.gibbsProbabilityReal x.1 *
      (L.singleLinkConditionalPMF x.1 e x.2).toReal *
      f (L.replaceLink x.1 e x.2) * g x.1
  let rhsTerm : (L.Configuration × L.Gauge) → ℝ := fun x =>
    L.gibbsProbabilityReal x.1 *
      (L.singleLinkConditionalPMF x.1 e x.2).toReal *
      f x.1 * g (L.replaceLink x.1 e x.2)
  change (∑ x, lhsTerm x) = ∑ x, rhsTerm x
  calc
    _ = ∑ x, rhsTerm (τ x) := by
      apply Finset.sum_congr rfl
      rintro ⟨A, h⟩ _
      simpa [lhsTerm, rhsTerm, τ,
        FiniteLatticeWilsonSystem.singleLinkUpdateSwapEquiv] using
        finite_lattice_singleLinkHeatBath_reversible_term L A e h f g
    _ = _ := τ.sum_comp rhsTerm

end

end MathlibAnalytic
end MGAP4D
