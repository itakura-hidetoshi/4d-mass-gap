import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTermBalance
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The forward Gibbs-weighted transition term for one exact link resampling. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathForwardTerm
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 e x.2).toReal *
    f (L.replaceLink x.1 e x.2) * g x.1

/-- The reversed Gibbs-weighted transition term for one exact link resampling. -/
def FiniteLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 e x.2).toReal *
    f x.1 * g (L.replaceLink x.1 e x.2)

/-- Pointwise detailed balance identifies a forward transition term with the
backward term evaluated after the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) :
    L.singleLinkHeatBathForwardTerm e f g x =
      L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x) := by
  rcases x with ⟨A, h⟩
  simpa [FiniteLatticeWilsonSystem.singleLinkHeatBathForwardTerm,
    FiniteLatticeWilsonSystem.singleLinkHeatBathBackwardTerm,
    FiniteLatticeWilsonSystem.singleLinkUpdateSwapEquiv] using
    finite_lattice_singleLinkHeatBath_reversible_term L A e h f g

/-- Exact detailed balance reindexes the full finite configuration--gauge
transition sum by the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_reversible_product_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g x := by
  classical
  calc
    _ = ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g
          (L.singleLinkUpdateSwapEquiv e x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
        L e f g x
    _ = _ := (L.singleLinkUpdateSwapEquiv e).sum_comp
      (L.singleLinkHeatBathBackwardTerm e f g)

end

end MathlibAnalytic
end MGAP4D
