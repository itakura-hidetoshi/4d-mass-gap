import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonFullSupportVarianceDefiniteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Energy of one selected plaquette as a real observable on physical positive-link
configurations. -/
def FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette) :
    L.Configuration → ℝ :=
  fun A => L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- A selected plaquette-energy observable is gauge invariant. -/
theorem finite_oriented_plaquetteEnergyObservable_gaugeInvariant
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.plaquetteEnergyObservable p (L.gaugeTransform gamma A) =
      L.plaquetteEnergyObservable p A := by
  unfold FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
  rw [finite_oriented_plaquetteHolonomy_gaugeTransform]
  exact L.plaquetteEnergy_conjInvariant _ _

/-- If one selected plaquette energy takes two distinct values, then its finite
Wilson Gibbs variance is strictly positive. -/
theorem finite_oriented_plaquetteEnergyObservable_gibbsVarianceReal_pos_of_exists_ne
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (A B : L.Configuration)
    (hNe : L.plaquetteEnergyObservable p A ≠
      L.plaquetteEnergyObservable p B) :
    0 < L.gibbsVarianceReal (L.plaquetteEnergyObservable p) :=
  finite_oriented_gibbsVarianceReal_pos_of_exists_ne
    L (L.plaquetteEnergyObservable p) A B hNe

end

end MathlibAnalytic
end MGAP4D
