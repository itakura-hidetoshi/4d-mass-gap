import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalGibbsL2Isometry
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroProductLawBCF

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

local instance canonicalBoundaryBetaZeroNormalizationNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryBetaZeroNormalizationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryBetaZeroNormalizationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryBetaZeroNormalizationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryBetaZeroNormalizationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryBetaZeroNormalizationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- In boundary/open-half/open-half coordinates, the zero-coupling finite
Wilson Gibbs density is identically one. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) :
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN 0 (by norm_num) z = 1 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  change ENNReal.ofReal
    (Real.exp
        (C.base.gibbsExponent
          (((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedPiMeasurableEquiv
            C.base.Gauge).symm z)) /
      C.base.partitionFunction) = 1
  rw [continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero
      C (by rfl),
    continuous_compact_oriented_partitionFunction_eq_one_of_beta_eq_zero
      C (by rfl)]
  norm_num

/-- The completed positive-half Gram feature becomes the constant one
function at zero coupling. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN 0 (by norm_num) b x = 1 := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity]
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_betaZero]
  norm_num

/-- The finite Wilson OS boundary vacuum wavefunction is identically one at
zero coupling. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryVacuumMoment
        H N hN 0 (by norm_num) b = 1 := by
  letI : IsProbabilityMeasure
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    unfold periodicHypercubicEvenOpenHalfHaarMeasure
    unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
    infer_instance
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  simp_rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_betaZero]
  simp

/-- The zero-coupling boundary marginal density is identically one. -/
theorem periodicHypercubicEvenBoundaryMarginalDensity_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryMarginalDensity
        H N hN 0 (by norm_num) b = 1 := by
  unfold periodicHypercubicEvenBoundaryMarginalDensity
  rw [periodicHypercubicEvenBoundaryVacuumMoment_betaZero]
  norm_num

/-- At zero coupling the interacting boundary marginal is exactly the boundary
product Haar probability law. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenBoundaryHaarMeasure H N := by
  unfold periodicHypercubicEvenBoundaryMarginalMeasure
  have hdensity :
      periodicHypercubicEvenBoundaryMarginalDensity
          H N hN 0 (by norm_num) = 1 := by
    funext b
    exact periodicHypercubicEvenBoundaryMarginalDensity_betaZero H N hN b
  rw [hdensity]
  simp

/-- The reciprocal boundary-vacuum normalization weight is one at zero
coupling. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2Weight_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
        H N hN 0 (by norm_num) b = 1 := by
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  rw [periodicHypercubicEvenBoundaryVacuumMoment_betaZero]
  simp

/-- Reciprocal-vacuum Haar-to-marginal transport has the original boundary
representative at zero coupling. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        H N hN 0 (by norm_num) f =ᵐ[
      periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN 0 (by norm_num)] f := by
  have htransport :=
    periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN 0 (by norm_num) f
  filter_upwards [htransport] with b hb
  rw [hb]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  rw [periodicHypercubicEvenBoundaryHaarToMarginalL2Weight_betaZero]
  simp

/-- The canonical OS-compatible boundary analysis has the plain boundary
restriction pullback representative at zero coupling. -/
theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_coeFn_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num) f =ᵐ[
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).gibbsMeasure]
      f ∘ (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction := by
  let J := periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
    H N hN 0 (by norm_num)
  let U := periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
    H N hN 0 (by norm_num)
  let hmp :=
    periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN 0 (by norm_num)
  change U (J f) =ᵐ[
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).gibbsMeasure]
    f ∘ (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
  have hpull :=
    periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry_coeFn
      H N hN 0 (by norm_num) (J f)
  have hboundary :=
    periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn_betaZero
      H N hN f
  have hboundaryPull := hmp.quasiMeasurePreserving.ae hboundary
  exact hpull.trans hboundaryPull

end

end MathlibAnalytic
end MGAP4D