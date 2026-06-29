import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathVariance
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditionalFiberInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Inserting the original physical-link value leaves the configuration
unchanged. -/
@[simp] theorem finite_oriented_replaceLink_original
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge) :
    L.replaceLink A e (A e) = A :=
  finite_oriented_replaceLink_current L A e

/-- The one-link Boltzmann weight at the original value is the global
Boltzmann weight. -/
@[simp] theorem finite_oriented_singleLinkBoltzmannWeight_original
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge) :
    L.singleLinkBoltzmannWeight A e (A e) =
      L.boltzmannWeight A := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    FiniteOrientedLatticeWilsonSystem.boltzmannWeight
  rw [finite_oriented_replaceLink_original]

/-- Exact reversible mass identity for native oriented one-link heat-bath
resampling. -/
theorem finite_oriented_singleLinkHeatBath_reversible_mass
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.gibbsPMF A * L.singleLinkConditionalPMF A e g =
      L.gibbsPMF (L.replaceLink A e g) *
        L.singleLinkConditionalPMF
          (L.replaceLink A e g) e (A e) := by
  rw [finite_oriented_singleLinkConditionalPMF_replaceLink]
  rw [finite_oriented_gibbsPMF_apply,
    finite_oriented_gibbsPMF_apply]
  rw [finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkConditionalPMF_apply]
  rw [finite_oriented_singleLinkBoltzmannWeight_original]
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    FiniteOrientedLatticeWilsonSystem.boltzmannWeight
  ac_rfl

/-- Real-valued detailed balance for the native oriented one-link kernel. -/
theorem finite_oriented_singleLinkHeatBath_detailedBalance_real
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e g).toReal =
      L.gibbsProbabilityReal (L.replaceLink A e g) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A e g) e (A e)).toReal := by
  change (L.gibbsPMF A).toReal *
      (L.singleLinkConditionalPMF A e g).toReal =
    (L.gibbsPMF (L.replaceLink A e g)).toReal *
      (L.singleLinkConditionalPMF
        (L.replaceLink A e g) e (A e)).toReal
  simpa only [ENNReal.toReal_mul] using
    congrArg ENNReal.toReal
      (finite_oriented_singleLinkHeatBath_reversible_mass L A e g)

end

end MathlibAnalytic
end MGAP4D
