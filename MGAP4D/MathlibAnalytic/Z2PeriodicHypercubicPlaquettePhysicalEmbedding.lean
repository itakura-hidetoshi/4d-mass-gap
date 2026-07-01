import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsIntegralVariance
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteVarianceTrajectory
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The finite oriented Wilson system carried by one scale of a periodic `Z₂`
plaquette trajectory. -/
noncomputable def Z2PeriodicHypercubicPlaquetteTrajectory.system
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) : FiniteOrientedLatticeWilsonSystem := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  exact z2PeriodicHypercubicOrientedWilsonSystem
    (T.sideLength k) (T.beta k) (T.beta_nonneg k)

/-- The selected gauge-invariant plaquette energy observable at one trajectory
scale, expressed on the trajectory's reconstructed finite system. -/
noncomputable def Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteObservable
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) :
    (T.system k).Configuration → ℝ := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  exact z2PeriodicHypercubicPlaquetteEnergyObservable
    (T.sideLength k) (T.beta k) (T.beta_nonneg k) (T.plaquette k)

/-- The trajectory variance is the Gibbs variance of the reconstructed finite
system and its selected plaquette observable. -/
theorem Z2PeriodicHypercubicPlaquetteTrajectory.gibbsVariance_eq_system
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) :
    T.gibbsVariance k =
      (T.system k).gibbsVarianceReal (T.plaquetteObservable k) := by
  unfold Z2PeriodicHypercubicPlaquetteTrajectory.gibbsVariance
    Z2PeriodicHypercubicPlaquetteTrajectory.system
    Z2PeriodicHypercubicPlaquetteTrajectory.plaquetteObservable
  rfl

/-- A concrete sequence of periodic `Z₂` Wilson Gibbs laws embedded into one
fixed physical Polish carrier, together with one physical bounded continuous
observable whose pullback is the selected plaquette energy at every scale. -/
structure Z2PeriodicHypercubicPlaquettePhysicalEmbedding where
  trajectory : Z2PeriodicHypercubicPlaquetteTrajectory
  PhysicalConfiguration : Type
  [physicalTopologicalSpace : TopologicalSpace PhysicalConfiguration]
  [physicalMeasurableSpace : MeasurableSpace PhysicalConfiguration]
  [physicalBorelSpace : BorelSpace PhysicalConfiguration]
  [physicalPolishSpace : PolishSpace PhysicalConfiguration]
  interpolate :
    ∀ k, (trajectory.system k).Configuration → PhysicalConfiguration
  interpolate_measurable : ∀ k, Measurable (interpolate k)
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ k, 0 < latticeSpacing k
  latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop
  observable : BoundedContinuousFunction PhysicalConfiguration ℝ
  observable_pullback :
    ∀ (k : ℕ) (A : (trajectory.system k).Configuration),
      observable (interpolate k A) = trajectory.plaquetteObservable k A
  betaUpper : ℝ
  beta_le : ∀ k, trajectory.beta k ≤ betaUpper

attribute [instance]
  Z2PeriodicHypercubicPlaquettePhysicalEmbedding.physicalTopologicalSpace
  Z2PeriodicHypercubicPlaquettePhysicalEmbedding.physicalMeasurableSpace
  Z2PeriodicHypercubicPlaquettePhysicalEmbedding.physicalBorelSpace
  Z2PeriodicHypercubicPlaquettePhysicalEmbedding.physicalPolishSpace

/-- Forget the periodic `Z₂` origin while retaining its exact finite Gibbs laws
and physical interpolation data. -/
noncomputable def Z2PeriodicHypercubicPlaquettePhysicalEmbedding.toLatticeEmbedding
    (P : Z2PeriodicHypercubicPlaquettePhysicalEmbedding) :
    PhysicalFourDimensionalYangMillsLatticeEmbedding :=
  { PhysicalConfiguration := P.PhysicalConfiguration
    LatticeConfiguration := fun k => (P.trajectory.system k).Configuration
    latticeMeasure := fun k => (P.trajectory.system k).gibbsProbabilityMeasure
    interpolate := P.interpolate
    interpolate_measurable := P.interpolate_measurable
    latticeSpacing := P.latticeSpacing
    latticeSpacing_pos := P.latticeSpacing_pos
    latticeSpacing_tendsto_zero := P.latticeSpacing_tendsto_zero
    physicalVolume := P.physicalVolume
    physicalVolume_tendsto_atTop := P.physicalVolume_tendsto_atTop }

/-- The pullback variance of the physical observable is exactly the finite
periodic `Z₂` plaquette Gibbs variance. -/
theorem Z2PeriodicHypercubicPlaquettePhysicalEmbedding.latticePullbackVariance_eq
    (P : Z2PeriodicHypercubicPlaquettePhysicalEmbedding)
    (k : ℕ) :
    P.toLatticeEmbedding.latticePullbackObservableVariance k P.observable =
      P.trajectory.gibbsVariance k := by
  let L := P.trajectory.system k
  let f := P.trajectory.plaquetteObservable k
  calc
    P.toLatticeEmbedding.latticePullbackObservableVariance k P.observable =
        (∫ A, f A ^ 2 ∂L.gibbsMeasure) -
          (∫ A, f A ∂L.gibbsMeasure) ^ 2 := by
      simpa [Z2PeriodicHypercubicPlaquettePhysicalEmbedding.toLatticeEmbedding,
        L, f] using
        physical_yang_mills_latticePullbackObservableVariance_eq_of_pointwise
          P.toLatticeEmbedding k P.observable f (P.observable_pullback k)
    _ = L.gibbsVarianceReal f :=
      (finite_oriented_gibbsVarianceReal_eq_secondMoment_sub_mean_sq L f).symm
    _ = P.trajectory.gibbsVariance k :=
      (P.trajectory.gibbsVariance_eq_system k).symm

/-- Any weak limit of the embedded periodic `Z₂` laws carries the realization
required by the bounded-coupling nontriviality theorem. -/
noncomputable def
    Z2PeriodicHypercubicPlaquettePhysicalEmbedding.toWeakLimitRealization
    (P : Z2PeriodicHypercubicPlaquettePhysicalEmbedding)
    (continuumMeasure : ProbabilityMeasure P.PhysicalConfiguration)
    (hWeak : Tendsto P.toLatticeEmbedding.embeddedMeasure atTop
      (nhds continuumMeasure)) :
    Z2PeriodicHypercubicPlaquetteWeakLimitRealization
      (P.toLatticeEmbedding.toWeakLimit continuumMeasure hWeak) :=
  { trajectory := P.trajectory
    observable := P.observable
    betaUpper := P.betaUpper
    beta_le := P.beta_le
    approximating_variance_eq := by
      intro k
      rw [physical_yang_mills_latticeEmbedding_approximatingObservableVariance_eq_pullback]
      exact P.latticePullbackVariance_eq k }

/-- Consequently, every supplied weak limit of a bounded-coupling physical
embedding has strictly positive continuum variance for the realized plaquette
observable. -/
theorem Z2PeriodicHypercubicPlaquettePhysicalEmbedding.continuum_variance_pos
    (P : Z2PeriodicHypercubicPlaquettePhysicalEmbedding)
    (continuumMeasure : ProbabilityMeasure P.PhysicalConfiguration)
    (hWeak : Tendsto P.toLatticeEmbedding.embeddedMeasure atTop
      (nhds continuumMeasure)) :
    0 < (P.toLatticeEmbedding.toWeakLimit continuumMeasure hWeak)
      .continuumObservableVariance P.observable :=
  (P.toWeakLimitRealization continuumMeasure hWeak).continuum_variance_pos

end

end MathlibAnalytic
end MGAP4D
