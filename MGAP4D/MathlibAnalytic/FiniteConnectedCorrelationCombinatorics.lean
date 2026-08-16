import MGAP4D.MathlibAnalytic.FiniteCumulantCombinatorics

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Connected finite correlation associated with a family of block moments.

For arbitrary finite order this is, by definition, the finite cumulant.  The
separate name records the interpretation used by the Euclidean/OS-facing layer
without identifying cumulants with centered products. -/
def finiteConnectedCorrelation
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) (moment : Finset α → R) : R :=
  finiteCumulant J moment

@[simp]
theorem finiteConnectedCorrelation_eq_finiteCumulant
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) (moment : Finset α → R) :
    finiteConnectedCorrelation J moment = finiteCumulant J moment := by
  rfl

/-- Pointwise equality of all block moments preserves the connected finite
correlation. -/
theorem finiteConnectedCorrelation_congr
    {α R : Type*} [DecidableEq α] [CommRing R]
    (J : Finset α) {moment moment' : Finset α → R}
    (h : ∀ B, moment' B = moment B) :
    finiteConnectedCorrelation J moment' = finiteConnectedCorrelation J moment := by
  exact finiteCumulant_congr J h

/-- Standard connected two-point combination `M₁₂ - M₁ M₂`.

This order-two surface is kept explicit because it is the covariance/connected
correlator used directly in decay and spectral arguments, whereas higher-order
connected functions use the full partition cumulant. -/
def finiteTwoPointConnected {R : Type*} [CommRing R]
    (pairMoment firstMoment secondMoment : R) : R :=
  pairMoment - firstMoment * secondMoment

/-- The connected two-point combination is functorial under equality of its
three input moments. -/
theorem finiteTwoPointConnected_congr
    {R : Type*} [CommRing R]
    {pairMoment pairMoment' firstMoment firstMoment' secondMoment secondMoment' : R}
    (hpair : pairMoment' = pairMoment)
    (hfirst : firstMoment' = firstMoment)
    (hsecond : secondMoment' = secondMoment) :
    finiteTwoPointConnected pairMoment' firstMoment' secondMoment' =
      finiteTwoPointConnected pairMoment firstMoment secondMoment := by
  simp [finiteTwoPointConnected, hpair, hfirst, hsecond]

end

end MathlibAnalytic
end MGAP4D
