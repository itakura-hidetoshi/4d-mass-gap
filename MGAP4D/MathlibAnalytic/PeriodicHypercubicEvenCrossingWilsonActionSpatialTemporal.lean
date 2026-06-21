import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionSectorDecomposition
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

/-- A crossing plaquette containing the Euclidean-time direction.  This is the
sector whose Wilson factors can subsequently be identified with relative
positive-half holonomy kernels. -/
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

/-- Time-containing bridge contribution to the crossing Wilson action. -/
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
part and its time-containing bridge part. -/
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

/-- Boltzmann weight of the purely spatial crossing-plane sector. -/
noncomputable def periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenSpatialCrossingWilsonAction H N A)

/-- Boltzmann weight of the time-containing bridge sector. -/
noncomputable def periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenTemporalCrossingWilsonAction H N A)

/-- The full crossing Boltzmann weight factors into the boundary spatial weight
and the temporal bridge weight. -/
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

end

end MathlibAnalytic
end MGAP4D
