import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance boundaryMarginalProbabilityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalProbabilityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalProbabilityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalProbabilitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalProbabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalProbabilityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The effective density introduced after integrating the two open halves is
exactly the boundary marginal density already appearing in the exact boundary
pushforward theorem.  This is a definitional compatibility theorem between the
#1648 effective-density surface and the earlier boundary-marginal surface. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_eq_marginalDensity
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b =
      periodicHypercubicEvenBoundaryMarginalDensity
        H N hN beta hbeta b := by
  rfl

/-- Tilting boundary Haar by the #1648 effective density gives exactly the
interacting boundary marginal measure constructed by the earlier pushforward
layer. -/
theorem periodicHypercubicEvenBoundaryHaar_withEffectiveDensity_eq_marginalMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
        (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta := by
  rfl

/-- The actual finite Wilson interacting boundary marginal is a probability
measure.  No new normalization integral is required: the marginal is the exact
pushforward of the already-normalized finite Wilson Gibbs measure under boundary
restriction. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) := by
  letI : IsProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
  rw [← periodicHypercubicEvenSpecialUnitary_map_boundaryRestriction_gibbsMeasure
    H N hN beta hbeta]
  exact Measure.isProbabilityMeasure_map
    (periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN beta hbeta).measurable.aemeasurable

/-- Export the probability normalization as a typeclass instance so downstream
weighted-L² constructions can use the actual boundary marginal directly. -/
instance periodicHypercubicEvenBoundaryMarginalMeasureProbability
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) :=
  periodicHypercubicEvenBoundaryMarginalMeasure_isProbabilityMeasure
    H N hN beta hbeta

/-- The earlier boundary marginal density therefore has ENNReal total mass
exactly one with respect to boundary Haar. -/
theorem periodicHypercubicEvenBoundaryMarginalDensity_lintegral_eq_one
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ b,
      periodicHypercubicEvenBoundaryMarginalDensity
        H N hN beta hbeta b
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) = 1 := by
  have hmass :
      periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta Set.univ = 1 := by
    simp
  unfold periodicHypercubicEvenBoundaryMarginalMeasure at hmass
  simpa using hmass

/-- Equivalently, the #1648 effective density itself has total ENNReal mass
one.  This is the normalized positive density required by the generic
with-density power-Gram machinery. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_lintegral_eq_one
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ b,
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) = 1 := by
  simpa only [periodicHypercubicEvenBoundaryMarginalEffectiveDensity_eq_marginalDensity]
    using periodicHypercubicEvenBoundaryMarginalDensity_lintegral_eq_one
      H N hN beta hbeta

/-- In particular the exact interacting boundary marginal supplies the finite
measure instance required by the generic positive-density power-Gram theorem. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_isFiniteMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) := by
  infer_instance

end

end MathlibAnalytic
end MGAP4D