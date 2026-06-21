import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionExactSectors
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionReflection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Reindexing a finite plaquette sum by the orientation-corrected reflection
permutation leaves the sum unchanged. -/
theorem periodicHypercubicEvenPlaquette_sum_reflection
    {M : Type*} [AddCommMonoid M]
    (H : ℕ) (f : PeriodicHypercubicEvenPlaquette H → M) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      f (periodicHypercubicEvenPlaquetteReflection H p)) =
      ∑ p : PeriodicHypercubicEvenPlaquette H, f p := by
  simpa [periodicHypercubicEvenPlaquetteReflectionEquiv] using
    (periodicHypercubicEvenPlaquetteReflectionEquiv H).sum_comp f

/-- Reflection exchanges the positive-open-half Wilson action with the exact
negative-open-half Wilson action. -/
theorem periodicHypercubicEvenPositiveWilsonAction_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenNegativeWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenPositiveWilsonAction
  unfold periodicHypercubicEvenNegativeWilsonAction
  calc
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      propositionIndicator
        (periodicHypercubicEvenStrictPositivePlaquette p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            (periodicHypercubicEvenConfigurationReflection H A) p))) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (periodicHypercubicEvenStrictPositivePlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [periodicHypercubicEvenWilsonPlaquetteEnergy_configurationReflection]
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (periodicHypercubicEvenStrictPositivePlaquette
            (periodicHypercubicEvenPlaquetteReflection H p))
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              simpa [periodicHypercubicEvenPlaquetteReflection_involutive] using
                (periodicHypercubicEvenPlaquette_sum_reflection H
                  (fun p : PeriodicHypercubicEvenPlaquette H =>
                    propositionIndicator
                      (periodicHypercubicEvenStrictPositivePlaquette
                        (periodicHypercubicEvenPlaquetteReflection H p))
                      (specialUnitaryWilsonPlaquetteEnergy N
                        (periodicHypercubicPlaquetteHolonomy A p))))
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (periodicHypercubicEvenStrictNegativePlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [periodicHypercubicEvenPlaquetteReflection_strictPositive_iff_strictNegative]

/-- Reflection exchanges the exact negative-open-half Wilson action with the
positive-open-half Wilson action. -/
theorem periodicHypercubicEvenNegativeWilsonAction_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPositiveWilsonAction H N A := by
  rw [← periodicHypercubicEvenPositiveWilsonAction_configurationReflection
    H N (periodicHypercubicEvenConfigurationReflection H A)]
  rw [periodicHypercubicEvenConfigurationReflection_involutive H A]

/-- Reflection preserves the crossing-plane Wilson action. -/
theorem periodicHypercubicEvenCrossingWilsonAction_configurationReflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenCrossingWilsonAction H N A := by
  have hreflected :=
    periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_exact_sector_decomposition
      H N hN 0 (by positivity)
      (periodicHypercubicEvenConfigurationReflection H A)
  have horiginal :=
    periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_exact_sector_decomposition
      H N hN 0 (by positivity) A
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection_invariant,
    periodicHypercubicEvenPositiveWilsonAction_configurationReflection,
    periodicHypercubicEvenNegativeWilsonAction_configurationReflection] at hreflected
  linarith

end

end MathlibAnalytic
end MGAP4D
