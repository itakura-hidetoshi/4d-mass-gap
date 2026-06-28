import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsSectorFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A crossing plaquette without the Euclidean-time direction.  These are the
purely spatial part of the reflection-plane sector and must be retained as a
boundary-dependent weight rather than treated as a relative half-lattice
kernel. -/
def periodicHypercubicEvenSpatialCrossingPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenCrossingPlaquette p ∧
    ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p

/-- A crossing plaquette containing the Euclidean-time direction.  This sector
is separated from the fixed-plane spatial weight before its precise
boundary/half-lattice dependence is analyzed. -/
def periodicHypercubicEvenTemporalCrossingPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenCrossingPlaquette p ∧
    periodicHypercubicEvenPlaquetteHasTimeDirection p

/-- Every crossing plaquette belongs to exactly one of the spatial and temporal
crossing sectors. -/
theorem periodicHypercubicEvenCrossingPlaquette_iff_spatial_or_temporal
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenCrossingPlaquette p ↔
      periodicHypercubicEvenSpatialCrossingPlaquette p ∨
        periodicHypercubicEvenTemporalCrossingPlaquette p := by
  unfold periodicHypercubicEvenSpatialCrossingPlaquette
  unfold periodicHypercubicEvenTemporalCrossingPlaquette
  by_cases ht : periodicHypercubicEvenPlaquetteHasTimeDirection p <;> simp [ht]

/-- The spatial and temporal crossing sectors are disjoint. -/
theorem periodicHypercubicEvenSpatialCrossingPlaquette_not_temporal
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (hs : periodicHypercubicEvenSpatialCrossingPlaquette p) :
    ¬ periodicHypercubicEvenTemporalCrossingPlaquette p := by
  intro ht
  exact hs.2 ht.2

/-- Orientation-corrected plaquette reflection preserves the purely spatial
crossing sector. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_spatialCrossing_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenSpatialCrossingPlaquette p := by
  simp [periodicHypercubicEvenSpatialCrossingPlaquette]

/-- Orientation-corrected plaquette reflection preserves the time-containing
crossing sector. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_temporalCrossing_iff
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenTemporalCrossingPlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenTemporalCrossingPlaquette p := by
  simp [periodicHypercubicEvenTemporalCrossingPlaquette]

/-- Purely spatial crossing-plane contribution to the Wilson action. -/
noncomputable def periodicHypercubicEvenSpatialCrossingWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenSpatialCrossingPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Time-containing contribution to the crossing Wilson action. -/
noncomputable def periodicHypercubicEvenTemporalCrossingWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenTemporalCrossingPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- The crossing Wilson action is exactly the sum of its fixed-plane spatial
part and its time-containing part. -/
theorem periodicHypercubicEvenCrossingWilsonAction_eq_spatial_add_temporal
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonAction H N A =
      periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenTemporalCrossingWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenCrossingWilsonAction
  unfold periodicHypercubicEvenSpatialCrossingWilsonAction
  unfold periodicHypercubicEvenTemporalCrossingWilsonAction
  change
    (∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
      propositionIndicator
        (periodicHypercubicEvenCrossingPlaquette p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p))) =
      (∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
        propositionIndicator
          (periodicHypercubicEvenSpatialCrossingPlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))) +
      ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
        propositionIndicator
          (periodicHypercubicEvenTemporalCrossingPlaquette p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hc : periodicHypercubicEvenCrossingPlaquette p <;>
    by_cases ht : periodicHypercubicEvenPlaquetteHasTimeDirection p <;>
      simp [propositionIndicator,
        periodicHypercubicEvenSpatialCrossingPlaquette,
        periodicHypercubicEvenTemporalCrossingPlaquette, hc, ht]

/-- A Wilson action restricted by any reflection-invariant plaquette predicate
is invariant under physical configuration reflection. -/
theorem periodicHypercubicEvenRestrictedWilsonAction_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (P : PeriodicHypercubicEvenPlaquette H → Prop)
    [DecidablePred P]
    (hP : ∀ p,
      P (periodicHypercubicEvenPlaquetteReflection H p) ↔ P p)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      propositionIndicator (P p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            (periodicHypercubicEvenConfigurationReflection H A) p))) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (P p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
  classical
  calc
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      propositionIndicator (P p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            (periodicHypercubicEvenConfigurationReflection H A) p))) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (P p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))) := by
                apply Finset.sum_congr rfl
                intro p _hp
                rw [periodicHypercubicEvenWilsonPlaquetteEnergy_configurationReflection]
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (P (periodicHypercubicEvenPlaquetteReflection H
            (periodicHypercubicEvenPlaquetteReflection H p)))
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))) := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [periodicHypercubicEvenPlaquetteReflection_involutive H p]
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (P (periodicHypercubicEvenPlaquetteReflection H p))
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              exact periodicHypercubicEvenPlaquette_sum_reflection H
                (fun p : PeriodicHypercubicEvenPlaquette H =>
                  propositionIndicator
                    (P (periodicHypercubicEvenPlaquetteReflection H p))
                    (specialUnitaryWilsonPlaquetteEnergy N
                      (periodicHypercubicPlaquetteHolonomy A p)))
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (P p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [hP p]

/-- The purely spatial fixed-plane crossing action is separately reflection
invariant. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonAction_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialCrossingWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenSpatialCrossingWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenSpatialCrossingWilsonAction
  simpa only using
    periodicHypercubicEvenRestrictedWilsonAction_configurationReflection
      H N periodicHypercubicEvenSpatialCrossingPlaquette
      (periodicHypercubicEvenPlaquetteReflection_spatialCrossing_iff H) A

/-- The time-containing crossing action is separately reflection invariant. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonAction_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenTemporalCrossingWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenTemporalCrossingWilsonAction
  simpa only using
    periodicHypercubicEvenRestrictedWilsonAction_configurationReflection
      H N periodicHypercubicEvenTemporalCrossingPlaquette
      (periodicHypercubicEvenPlaquetteReflection_temporalCrossing_iff H) A

/-- Boltzmann weight of the purely spatial crossing-plane sector. -/
noncomputable def periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenSpatialCrossingWilsonAction H N A)

/-- Boltzmann weight of the time-containing crossing sector. -/
noncomputable def periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenTemporalCrossingWilsonAction H N A)

/-- The full crossing Boltzmann weight factors into the spatial fixed-plane
weight and the time-containing weight. -/
theorem periodicHypercubicEvenCrossingWilsonBoltzmannWeight_eq_spatial_mul_temporal
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta A =
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A *
        periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
  rw [periodicHypercubicEvenCrossingWilsonAction_eq_spatial_add_temporal]
  rw [show -beta *
      (periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenTemporalCrossingWilsonAction H N A) =
      (-beta * periodicHypercubicEvenSpatialCrossingWilsonAction H N A) +
        (-beta * periodicHypercubicEvenTemporalCrossingWilsonAction H N A) by ring]
  rw [Real.exp_add]

/-- The purely spatial crossing Boltzmann weight is separately reflection
invariant. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
  rw [periodicHypercubicEvenSpatialCrossingWilsonAction_configurationReflection]

/-- The time-containing crossing Boltzmann weight is separately reflection
invariant. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
  rw [periodicHypercubicEvenTemporalCrossingWilsonAction_configurationReflection]

end

end MathlibAnalytic
end MGAP4D
