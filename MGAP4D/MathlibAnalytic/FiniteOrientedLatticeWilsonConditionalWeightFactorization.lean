import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalLocalFactor

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every exact single-link weight factors into its target-local part and a
common target-remote factor. -/
theorem finite_oriented_singleLinkBoltzmannWeight_eq_local_mul_remote
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.singleLinkBoltzmannWeight A target g =
      L.targetLocalSingleLinkBoltzmannWeight A target g *
        L.targetRemoteBoltzmannFactor A target := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
    FiniteOrientedLatticeWilsonSystem.targetRemoteBoltzmannFactor
  rw [finite_oriented_wilsonAction_replaceLink_eq_local_add_remote]
  have hArg :
      -L.beta *
          (L.targetLocalPlaquetteAction
              (L.replaceLink A target g) target +
            L.targetRemotePlaquetteAction A target) =
        -L.beta *
            L.targetLocalPlaquetteAction
              (L.replaceLink A target g) target +
          -L.beta * L.targetRemotePlaquetteAction A target := by
    ring
  rw [hArg, Real.exp_add,
    ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]

end

end MathlibAnalytic
end MGAP4D
