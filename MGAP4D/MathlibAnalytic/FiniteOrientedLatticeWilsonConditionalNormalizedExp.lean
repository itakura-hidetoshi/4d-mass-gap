import MGAP4D.MathlibAnalytic.FiniteNormalizedExponentialOscillation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalRemoteCancellation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real log-weight of the exact target-local oriented Wilson conditional. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ :=
  -L.beta *
    L.targetLocalPlaquetteAction (L.replaceLink A target g) target

/-- The real value of the target-local partition function is the finite
partition of its real log-weights. -/
theorem finite_oriented_targetLocalSingleLinkPartitionFunction_toReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    (L.targetLocalSingleLinkPartitionFunction A target).toReal =
      finiteExpPartition (L.targetLocalSingleLinkLogWeight A target) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
    finiteExpPartition
  rw [tsum_fintype]
  calc
    ENNReal.toReal
        (∑ g : L.Gauge,
          L.targetLocalSingleLinkBoltzmannWeight A target g) =
      ∑ g : L.Gauge,
        (L.targetLocalSingleLinkBoltzmannWeight A target g).toReal := by
          exact ENNReal.toReal_sum
            (fun g _hg => by
              simp
                [FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight])
    _ = ∑ g : L.Gauge,
        Real.exp (L.targetLocalSingleLinkLogWeight A target g) := by
      apply Finset.sum_congr rfl
      intro g _hg
      simp
        [FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight,
          FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight] <;>
        positivity

/-- The exact oriented single-link conditional PMF, after remote-factor
cancellation, is the normalized real exponential of the target-local
log-weight. -/
theorem finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    (L.singleLinkConditionalPMF A target g).toReal =
      finiteNormalizedExp (L.targetLocalSingleLinkLogWeight A target) g := by
  rw [finite_oriented_singleLinkConditionalPMF_eq_targetLocal,
    finite_oriented_targetLocalSingleLinkConditionalPMF_apply]
  unfold finiteNormalizedExp
    FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    finite_oriented_targetLocalSingleLinkPartitionFunction_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
  rw [div_eq_mul_inv]

end

end MathlibAnalytic
end MGAP4D
