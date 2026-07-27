import MGAP4D.MathlibAnalytic.LinearMarkovIntegerCenteredPathProjectiveFamily

namespace MGAP4D
namespace MathlibAnalytic

example {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n d : ℕ) :
    (linearMarkovFinitePathPMF initial transition (2 * (n + d) + 2)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        linearMarkovFinitePathPMF initial transition (2 * n + 2) :=
  linearMarkovFinitePathPMF_map_integerCenteredRestrictBy_of_detailedBalance
    initial transition hdb n d

end MathlibAnalytic
end MGAP4D
