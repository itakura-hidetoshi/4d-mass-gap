import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathConsistency

namespace MGAP4D
namespace MathlibAnalytic

example
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovChronologicalCenteredFinitePathPMF
        initial transition (n + 1)).map
          linearMarkovChronologicalCenteredFinitePathInit =
      linearMarkovChronologicalCenteredFinitePathPMF
        initial transition n :=
  linearMarkovChronologicalCenteredFinitePathPMF_succ_map_init_of_detailedBalance
    initial transition hdb n

end MathlibAnalytic
end MGAP4D
