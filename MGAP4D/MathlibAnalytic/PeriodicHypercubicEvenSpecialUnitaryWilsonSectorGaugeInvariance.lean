import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNormalizedTracePowerGaugeInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Wilson action restricted by an arbitrary plaquette selector on the actual
even-periodic `SU(N)` lattice. -/
noncomputable def periodicHypercubicEvenSelectedWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (selected : PeriodicHypercubicEvenPlaquette H → Prop)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator (selected p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Every finite proposition-selected sum of actual Wilson plaquette energies is
gauge invariant.  The selector is purely geometric and therefore unchanged;
each selected summand is invariant because the actual oriented plaquette
holonomy transforms by conjugation. -/
theorem periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : PeriodicHypercubicEvenPlaquette H → Prop)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSelectedWilsonAction H N selected
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenSelectedWilsonAction H N selected A := by
  classical
  unfold periodicHypercubicEvenSelectedWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hs : selected p
  · simp only [propositionIndicator, if_pos hs]
    change
      specialUnitaryWilsonPlaquetteEnergy N
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.plaquetteHolonomy
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
              gamma A) p) =
        specialUnitaryWilsonPlaquetteEnergy N
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.plaquetteHolonomy
            A p)
    rw [compact_oriented_plaquetteHolonomy_gaugeTransform]
    exact specialUnitaryWilsonPlaquetteEnergy_conjInvariant _ _
  · simp [propositionIndicator, hs]

/-- The strict-positive Wilson action is gauge invariant. -/
theorem periodicHypercubicEvenPositiveWilsonAction_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonAction H N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveWilsonAction H N A := by
  simpa [periodicHypercubicEvenPositiveWilsonAction,
    periodicHypercubicEvenSelectedWilsonAction] using
    periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
      H N hN beta hbeta periodicHypercubicEvenStrictPositivePlaquette gamma A

/-- The strict-negative Wilson action is gauge invariant. -/
theorem periodicHypercubicEvenNegativeWilsonAction_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeWilsonAction H N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenNegativeWilsonAction H N A := by
  simpa [periodicHypercubicEvenNegativeWilsonAction,
    periodicHypercubicEvenSelectedWilsonAction] using
    periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
      H N hN beta hbeta periodicHypercubicEvenStrictNegativePlaquette gamma A

/-- The purely spatial crossing action is gauge invariant. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonAction_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialCrossingWilsonAction H N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenSpatialCrossingWilsonAction H N A := by
  simpa [periodicHypercubicEvenSpatialCrossingWilsonAction,
    periodicHypercubicEvenSelectedWilsonAction] using
    periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
      H N hN beta hbeta periodicHypercubicEvenSpatialCrossingPlaquette gamma A

/-- The positive-boundary temporal Wilson action is gauge invariant. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A := by
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction,
    periodicHypercubicEvenSelectedWilsonAction] using
    periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
      H N hN beta hbeta
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette gamma A

/-- The negative-boundary temporal Wilson action is gauge invariant. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A := by
  simpa [periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction,
    periodicHypercubicEvenSelectedWilsonAction] using
    periodicHypercubicEvenSelectedWilsonAction_gaugeInvariant
      H N hN beta hbeta
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette gamma A

/-- The strict-positive Boltzmann amplitude is gauge invariant. -/
theorem periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta A := by
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonAction_gaugeInvariant H N hN beta hbeta]

/-- The purely spatial crossing Boltzmann weight is gauge invariant. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  rw [periodicHypercubicEvenSpatialCrossingWilsonAction_gaugeInvariant H N hN beta hbeta]

/-- The positive-boundary temporal Boltzmann weight is gauge invariant. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_gaugeInvariant
    H N hN beta hbeta]

end

end MathlibAnalytic
end MGAP4D
