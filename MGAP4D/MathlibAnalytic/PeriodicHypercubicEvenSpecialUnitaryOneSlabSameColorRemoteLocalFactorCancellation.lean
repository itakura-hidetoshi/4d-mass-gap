import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorPlaquetteSeparation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Distinct right-boundary spatial links in one six-color class do not
interact in the exact target-local Boltzmann factor of the one-slab Wilson
kernel.

This is a raw-kernel statement.  It does not assert the corresponding
continuous-vacuum weight is independent of the remote source after integration
against the top eigenvector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_sameColor_remote_update_eq
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (h k g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B source h) target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B source k) target g := by
  classical
  have hCommH :
      Function.update (Function.update B source h) target g =
        Function.update (Function.update B target g) source h := by
    funext e
    by_cases heTarget : e = target
    · subst e
      simp [hne, Ne.symm hne]
    · by_cases heSource : e = source
      · subst e
        simp [hne, Ne.symm hne]
      · simp [heTarget, heSource]
  have hCommK :
      Function.update (Function.update B source k) target g =
        Function.update (Function.update B target g) source k := by
    funext e
    by_cases heTarget : e = target
    · subst e
      simp [hne, Ne.symm hne]
    · by_cases heSource : e = source
      · subst e
        simp [hne, Ne.symm hne]
      · simp [heTarget, heSource]
  have hUpdated :
      (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update (Function.update B source h) target g) p)) =
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update (Function.update B source k) target g) p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpTarget :
        periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target :=
      (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff
        H target p).1 hp
    have hpNotSource :
        ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source := by
      intro hpSource
      apply hne
      exact periodicHypercubicEvenSpatialSliceLink_sameColor_touches_eq
        H (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
        hpTarget hpSource hColor
    have hh :
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update (Function.update B source h) target g) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B target g) p := by
      rw [hCommH]
      simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N (Function.update B target g) source h p hpNotSource)
    have hk :
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update (Function.update B source k) target g) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B target g) p := by
      rw [hCommK]
      simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N (Function.update B target g) source k p hpNotSource)
    rw [hh, hk]
  have hBase :
      (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B source h) p)) =
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B source k) p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpTarget :
        periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target :=
      (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff
        H target p).1 hp
    have hpNotSource :
        ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p source := by
      intro hpSource
      apply hne
      exact periodicHypercubicEvenSpatialSliceLink_sameColor_touches_eq
        H (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
        hpTarget hpSource hColor
    have hh :
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B source h) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p := by
      simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N B source h p hpNotSource)
    have hk :
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update B source k) p =
          periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p := by
      simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N B source k p hpNotSource)
    rw [hh, hk]
  have hSpatial :
      (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update (Function.update B source h) target g) p)) -
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B source h) p) =
      (∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update (Function.update B source k) target g) p)) -
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B source k) p) := by
    rw [hUpdated, hBase]
  simp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
    hne, Ne.symm hne, hSpatial]

end

end MathlibAnalytic
end MGAP4D
