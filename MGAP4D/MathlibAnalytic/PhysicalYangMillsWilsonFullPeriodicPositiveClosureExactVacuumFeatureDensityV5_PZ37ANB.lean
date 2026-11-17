import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureMarginalV5_PZ37ANB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveHalfFiberV5_PZ37ANB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANB — exact full-periodic positive-closure Wilson density

The actual normalized full-periodic SU(N) Wilson Gibbs law, restricted to the
shared reflection-fixed boundary and the positive open half, has density
ENNReal.ofReal (boundaryVacuumMoment(b) * completedPositiveGramFeature(b,x))
with respect to the unchanged independent product Haar measure.

Both the real negative-half fiber identity and the exact full-periodic
measure-map statement are previously certified. Here they are connected
without assuming the ANA normalized temporal-gauge path law or any OS state.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANB_exactDensity_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance p4Q2PZ37ANB_exactDensity_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37ANB_exactDensity_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37ANB_exactDensity_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37ANB_exactDensity_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37ANB_exactDensity_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Genuine normalized periodic Gibbs negative-half fiber lintegral equals
the real completed boundary-vacuum times positive-half Gram feature,
embedded into ENNReal. No separate conditional measure is assumed. -/
theorem p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_lintegral_eq_ofReal_vacuum_mul_feature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    (∫⁻ y,
      periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ENNReal.ofReal
        (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let μ := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let ρ := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  let f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ :=
    fun y => (ρ (b, (x, y))).toReal
  letI : IsFiniteMeasure μ := by
    dsimp [μ, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hMeas : Measurable f := by
    dsimp [f]
    have hd : Measurable ρ :=
      periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
        H N hN beta hbeta
    exact (ENNReal.measurable_toReal.comp hd).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hBound : ∀ y, ‖f y‖ ≤ C.base.partitionFunction⁻¹ := by
    intro y
    dsimp [f]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa [ρ, C] using
      periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
        H N hN beta hbeta (b, (x, y))
  have hInt : Integrable f μ :=
    Integrable.of_bound hMeas.aestronglyMeasurable C.base.partitionFunction⁻¹
      (Filter.Eventually.of_forall hBound)
  have hNonneg : 0 ≤ᵐ[μ] f :=
    Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg
  have hOfReal (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
      ENNReal.ofReal (f y) = ρ (b, (x, y)) := by
    dsimp [f, ρ, periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity,
      ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity]
    rw [ENNReal.toReal_ofReal]
    exact div_nonneg (Real.exp_nonneg _) hZ.le
  calc
    (∫⁻ y, ρ (b, (x, y)) ∂μ) =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μ := by
      apply lintegral_congr
      intro y
      exact (hOfReal y).symm
    _ = ENNReal.ofReal (∫ y, f y ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
    _ = ENNReal.ofReal
          (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b *
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta b x) := by
      congr 1
      exact p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_eq_vacuum_mul_feature
        H N hN beta hbeta b x

/-- Exact positive-closure marginal of the genuine normalized full-periodic
Wilson Gibbs probability as a single explicit vacuum × Gram-feature
density on original boundary/open-half product Haar. -/
theorem p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal_eq_vacuum_mul_feature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
           (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)).withDensity
          (fun z => ENNReal.ofReal
            (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta z.1 *
             periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
               H N hN beta hbeta z.1 z.2)) := by
  rw [p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal]
  have hEq :
      (fun z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        ∫⁻ y,
          periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta (z.1, (z.2, y))
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
        (fun z => ENNReal.ofReal
          (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta z.1 *
           periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
             H N hN beta hbeta z.1 z.2)) := by
    funext z
    exact p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_lintegral_eq_ofReal_vacuum_mul_feature
      H N hN beta hbeta z.1 z.2
  rw [hEq]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_lintegral_eq_ofReal_vacuum_mul_feature
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal_eq_vacuum_mul_feature
