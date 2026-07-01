import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquettePhysicalEmbedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

theorem Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteObservable_eq_zero_or_one
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ)
    (A : (T.system k).Configuration) :
    T.plaquetteObservable k A = 0 ∨ T.plaquetteObservable k A = 1 := by
  simpa [Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteObservable,
    Z2PeriodicHypercubicPlaquetteTrajectory.system,
    z2PeriodicHypercubicPlaquetteEnergyObservable,
    FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable,
    z2PeriodicHypercubicOrientedWilsonSystem] using
    (Classical.em
      ((T.system k).plaquetteHolonomy A (T.plaquette k) = 1))

def Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteBit
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ)
    (A : (T.system k).Configuration) : Bool := by
  classical
  exact decide (T.plaquetteObservable k A = 1)

def z2BinaryPlaquetteObservable : BoundedContinuousFunction Bool ℝ :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun b : Bool => if b then 1 else 0) 1 (by
      intro x y
      fin_cases x <;> fin_cases y <;> norm_num [Real.dist_eq])

@[simp]
theorem z2BinaryPlaquetteObservable_apply
    (b : Bool) :
    z2BinaryPlaquetteObservable b = if b then 1 else 0 := by
  rfl

theorem Z2PeriodicHypercubicPlaquetteTrajectory.binaryObservable_pullback
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ)
    (A : (T.system k).Configuration) :
    z2BinaryPlaquetteObservable (T.plaquetteBit k A) =
      T.plaquetteObservable k A := by
  classical
  rcases T.plaquetteObservable_eq_zero_or_one k A with hZero | hOne
  · simp [Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteBit, hZero]
  · simp [Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteBit, hOne]

structure Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData where
  trajectory : Z2PeriodicHypercubicPlaquetteTrajectory
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ k, 0 < latticeSpacing k
  latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop
  betaUpper : ℝ
  beta_le : ∀ k, trajectory.beta k ≤ betaUpper

noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.toPhysicalEmbedding
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Z2PeriodicHypercubicPlaquettePhysicalEmbedding :=
  { trajectory := D.trajectory
    PhysicalConfiguration := Bool
    interpolate := D.trajectory.plaquetteBit
    interpolate_measurable := fun _ => measurable_of_finite _
    latticeSpacing := D.latticeSpacing
    latticeSpacing_pos := D.latticeSpacing_pos
    latticeSpacing_tendsto_zero := D.latticeSpacing_tendsto_zero
    physicalVolume := D.physicalVolume
    physicalVolume_tendsto_atTop := D.physicalVolume_tendsto_atTop
    observable := z2BinaryPlaquetteObservable
    observable_pullback := D.trajectory.binaryObservable_pullback
    betaUpper := D.betaUpper
    beta_le := D.beta_le }

theorem Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.continuum_variance_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (continuumMeasure : ProbabilityMeasure Bool)
    (hWeak : Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
      atTop (nhds continuumMeasure)) :
    0 < PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
      (D.toPhysicalEmbedding.toLatticeEmbedding.toWeakLimit
        continuumMeasure hWeak)
      z2BinaryPlaquetteObservable :=
  D.toPhysicalEmbedding.continuum_variance_pos continuumMeasure hWeak

end

end MathlibAnalytic
end MGAP4D
