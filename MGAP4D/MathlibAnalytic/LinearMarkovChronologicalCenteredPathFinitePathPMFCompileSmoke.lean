import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathFinitePathPMF

namespace MGAP4D
namespace MathlibAnalytic

example
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    linearMarkovChronologicalCenteredFinitePathPMF initial transition n =
      linearMarkovFinitePathPMF initial transition (2 * n + 2) :=
  linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    initial transition n

end MathlibAnalytic
end MGAP4D
