import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalGibbsL2Isometry

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

local instance boundaryVacuumL2NeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryVacuumL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryVacuumL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryVacuumL2SecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryVacuumL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryVacuumL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The interacting Wilson boundary marginal is a probability measure because
it is the exact pushforward of the finite Gibbs probability law. -/
noncomputable instance periodicHypercubicEvenBoundaryMarginal_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta) := by
  let hprob : IsProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
  let hmp :=
    periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN beta hbeta
  refine ⟨?_⟩
  have hpre := hmp.measure_preimage MeasurableSet.univ
  exact hpre.symm.trans (by
    simpa only [Set.preimage_univ] using hprob.measure_univ)

/-- The finite Wilson OS boundary vacuum wavefunction belongs to boundary Haar
`L²`.  Its squared norm density is precisely the interacting boundary
marginal density. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_memLp
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  apply (memLp_two_iff_integrable_sq
    (periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).aestronglyMeasurable).2
  have hone : Integrable
      (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        (1 : ℝ))
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta) :=
    integrable_const _
  rw [periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    H N hN beta hbeta] at hone
  rw [integrable_withDensity_iff_integrable_smul
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H N hN beta hbeta)] at hone
  apply hone.congr
  filter_upwards with b
  change
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
      H N hN beta hbeta b : ℝ) * 1 =
      periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b ^ 2
  unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
  rw [mul_one]
  exact Real.coe_toNNReal _ (sq_nonneg _)

/-- The actual finite Wilson boundary vacuum vector in boundary Haar `L²`. -/
noncomputable def periodicHypercubicEvenBoundaryVacuumL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  (periodicHypercubicEvenBoundaryVacuumMoment_memLp
    H N hN beta hbeta).toLp
    (periodicHypercubicEvenBoundaryVacuumMoment
      H N hN beta hbeta)

/-- The boundary vacuum `L²` representative is the concrete Gram vacuum
moment. -/
theorem periodicHypercubicEvenBoundaryVacuumL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryVacuumL2
      H N hN beta hbeta =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure H N]
      periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta :=
  MemLp.coeFn_toLp
    (periodicHypercubicEvenBoundaryVacuumMoment_memLp
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
