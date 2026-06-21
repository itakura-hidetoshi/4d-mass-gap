import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteHolonomyReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.Algebra.BigOperators.Group.Finset

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Orientation-corrected plaquette reflection as a permutation of all
plaquette labels. -/
def periodicHypercubicEvenPlaquetteReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenPlaquette H ≃
      PeriodicHypercubicEvenPlaquette H :=
  (periodicHypercubicEvenPlaquetteReflection_involutive H).toPerm

@[simp]
theorem periodicHypercubicEvenPlaquetteReflectionEquiv_apply
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPlaquetteReflectionEquiv H p =
      periodicHypercubicEvenPlaquetteReflection H p :=
  rfl

/-- Every individual standard `SU(N)` Wilson plaquette energy is preserved by
site reflection of the physical positive-link configuration. -/
theorem periodicHypercubicEvenWilsonPlaquetteEnergy_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy
          (periodicHypercubicEvenConfigurationReflection H A) p) =
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPlaquetteReflection H p)) := by
  by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection p
  · rw [periodicHypercubicEvenPlaquetteHolonomy_configurationReflection_of_hasTimeDirection
      H A p htime]
    calc
      specialUnitaryWilsonPlaquetteEnergy N
          ((A ((periodicHypercubicEvenPlaquetteReflection H p).1, 0))⁻¹ *
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))⁻¹ *
            A ((periodicHypercubicEvenPlaquetteReflection H p).1, 0)) =
        specialUnitaryWilsonPlaquetteEnergy N
          ((periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenPlaquetteReflection H p))⁻¹) := by
              simpa using
                (specialUnitaryWilsonPlaquetteEnergy_conjInvariant
                  (N := N)
                  (A ((periodicHypercubicEvenPlaquetteReflection H p).1, 0))⁻¹
                  ((periodicHypercubicPlaquetteHolonomy A
                    (periodicHypercubicEvenPlaquetteReflection H p))⁻¹))
      _ = specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenPlaquetteReflection H p)) :=
        specialUnitaryWilsonPlaquetteEnergy_inv
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenPlaquetteReflection H p))
  · rw [periodicHypercubicEvenPlaquetteHolonomy_configurationReflection_of_not_hasTimeDirection
      H A p htime]

/-- The actual finite-volume even-periodic `SU(N)` Wilson action is invariant
under site reflection of physical positive-link configurations. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection_invariant
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.wilsonAction
      (periodicHypercubicEvenConfigurationReflection H A) =
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.wilsonAction A := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction,
    periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction]
  calc
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy
          (periodicHypercubicEvenConfigurationReflection H A) p)) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenPlaquetteReflection H p)) := by
              apply Finset.sum_congr rfl
              intro p hp
              exact periodicHypercubicEvenWilsonPlaquetteEnergy_configurationReflection
                H N A p
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p) := by
            simpa [periodicHypercubicEvenPlaquetteReflectionEquiv] using
              (periodicHypercubicEvenPlaquetteReflectionEquiv H).sum_comp
                (fun p : PeriodicHypercubicEvenPlaquette H =>
                  specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicPlaquetteHolonomy A p))

end

end MathlibAnalytic
end MGAP4D
