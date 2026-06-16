import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTermBalance

namespace MGAP4D
namespace MathlibAnalytic

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

end

end MathlibAnalytic
end MGAP4D
