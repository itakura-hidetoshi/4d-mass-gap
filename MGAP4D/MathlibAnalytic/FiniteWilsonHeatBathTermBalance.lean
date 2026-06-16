import MGAP4D.MathlibAnalytic.FiniteWilsonLinkExchange

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The first component of the involutive link exchange restores the original
configuration. -/
@[simp] theorem finite_lattice_singleLinkUpdateSwap_first_roundTrip
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge) :
    L.replaceLink (L.replaceLink A e h) e (A e) = A := by
  simpa [FiniteLatticeWilsonSystem.singleLinkUpdateSwapEquiv] using
    congrArg Prod.fst
      ((L.singleLinkUpdateSwapEquiv e).left_inv (A, h))

/-- Pointwise reversibility of the Gibbs-weighted single-link transition term. -/
theorem finite_lattice_singleLinkHeatBath_reversible_term
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge)
    (f g : L.Configuration → ℝ) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e h).toReal *
        f (L.replaceLink A e h) * g A =
      L.gibbsProbabilityReal (L.replaceLink A e h) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A e h) e (A e)).toReal *
        f (L.replaceLink A e h) *
        g (L.replaceLink (L.replaceLink A e h) e (A e)) := by
  rw [finite_lattice_singleLinkHeatBath_detailedBalance_real]
  rw [finite_lattice_singleLinkUpdateSwap_first_roundTrip]

end

end MathlibAnalytic
end MGAP4D
