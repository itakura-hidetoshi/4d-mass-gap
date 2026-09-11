import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalPMF

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

#check linearMarkovIntegerCenteredFinitePathRestrictBy_apply
#check linearMarkovIntegerFiniteMarginalPMF_projective

example {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (I J : Finset ℤ) (hJI : J ⊆ I) :
    linearMarkovIntegerFiniteMarginalPMF initial transition J =
      (linearMarkovIntegerFiniteMarginalPMF initial transition I).map
        (@Finset.restrict₂ ℤ (fun _ => Ω) J I hJI) :=
  linearMarkovIntegerFiniteMarginalPMF_projective
    initial transition hdb I J hJI

end

end MathlibAnalytic
end MGAP4D
