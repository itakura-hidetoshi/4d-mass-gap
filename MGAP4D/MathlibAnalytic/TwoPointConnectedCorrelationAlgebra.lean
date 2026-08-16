import Mathlib.Algebra.Ring.Defs

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Algebraic two-point connected correlation associated with a pair moment and
the corresponding one-point moments.

This is the standard second cumulant formula `M₁₂ - M₁ M₂`, isolated from any
probabilistic or field-theoretic structure. -/
def twoPointConnectedCorrelation
    {R : Type*} [CommRing R]
    (pairMoment leftMoment rightMoment : R) : R :=
  pairMoment - leftMoment * rightMoment

/-- The two-point connected-correlation expression is functorial under equality
of the pair and one-point moments. -/
theorem twoPointConnectedCorrelation_congr
    {R : Type*} [CommRing R]
    {pairMoment pairMoment' leftMoment leftMoment' rightMoment rightMoment' : R}
    (hpair : pairMoment' = pairMoment)
    (hleft : leftMoment' = leftMoment)
    (hright : rightMoment' = rightMoment) :
    twoPointConnectedCorrelation pairMoment' leftMoment' rightMoment' =
      twoPointConnectedCorrelation pairMoment leftMoment rightMoment := by
  simp [twoPointConnectedCorrelation, hpair, hleft, hright]

end

end MathlibAnalytic
end MGAP4D
