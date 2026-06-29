import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pre-updating the resampled physical link leaves its conditional law
unchanged. -/
theorem finite_oriented_singleLinkConditionalPMF_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.singleLinkConditionalPMF (L.replaceLink A target g) target =
      L.singleLinkConditionalPMF A target := by
  symm
  apply finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
  exact finite_oriented_agreeOffLink_replaceLink L A target g

/-- Inserting the original physical-link value recovers the original global
Boltzmann weight. -/
@[simp] theorem finite_oriented_singleLinkBoltzmannWeight_original
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkBoltzmannWeight A target (A target) =
      L.boltzmannWeight A := by
  rw [finite_oriented_singleLinkBoltzmannWeight_eq_boltzmannWeight_replaceLink,
    finite_oriented_replaceLink_current]

/-- Exact reversible-mass identity for one orientation-correct physical-link
heat-bath update. -/
theorem finite_oriented_singleLinkHeatBath_reversible_mass
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.gibbsPMF A * L.singleLinkConditionalPMF A target g =
      L.gibbsPMF (L.replaceLink A target g) *
        L.singleLinkConditionalPMF
          (L.replaceLink A target g) target (A target) := by
  rw [finite_oriented_singleLinkConditionalPMF_replaceLink]
  rw [finite_oriented_gibbsPMF_apply, finite_oriented_gibbsPMF_apply]
  rw [finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkConditionalPMF_apply]
  rw [finite_oriented_singleLinkBoltzmannWeight_original]
  rw [finite_oriented_singleLinkBoltzmannWeight_eq_boltzmannWeight_replaceLink]
  ac_rfl

/-- Real-valued detailed balance for the exact orientation-correct one-link
heat-bath update. -/
theorem finite_oriented_singleLinkHeatBath_detailedBalance_real
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A target g).toReal =
      L.gibbsProbabilityReal (L.replaceLink A target g) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A target g) target (A target)).toReal := by
  change (L.gibbsPMF A).toReal *
      (L.singleLinkConditionalPMF A target g).toReal =
    (L.gibbsPMF (L.replaceLink A target g)).toReal *
      (L.singleLinkConditionalPMF
        (L.replaceLink A target g) target (A target)).toReal
  simpa only [ENNReal.toReal_mul] using
    congrArg ENNReal.toReal
      (finite_oriented_singleLinkHeatBath_reversible_mass L A target g)

end

end MathlibAnalytic
end MGAP4D
