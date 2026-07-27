import MGAP4D.MathlibAnalytic.LinearMarkovSingleChainCenteredTimeReflectionPMF

namespace MGAP4D
namespace MathlibAnalytic

example
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    linearMarkovSingleChainCenteredFinitePathPMF initial transition n =
      linearMarkovCenteredFinitePathPMF initial transition n :=
  linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
    initial transition hdb n

end MathlibAnalytic
end MGAP4D
