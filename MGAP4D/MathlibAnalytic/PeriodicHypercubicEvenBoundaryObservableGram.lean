import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBochnerGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts
import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

noncomputable def periodicHypercubicEvenBoundaryObservableGramFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b x * f x

theorem periodicHypercubicEvenBoundaryDensity_mul_observable_eq_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y) =
      inner ℝ
        (periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f b x)
        (periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f b y) := by
  rw [periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner]
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  simp only [periodicHypercubicEven_real_inner_eq_mul]
  ring

/-- On the reflected diagonal, the boundary-conditioned Wilson Gibbs observable
kernel is exactly the square of its scalar Gram feature. -/
theorem periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_eq_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal *
        (f x * f x) =
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x) ^ 2 := by
  rw [periodicHypercubicEvenBoundaryDensity_mul_observable_eq_inner]
  rw [periodicHypercubicEven_real_inner_eq_mul]
  rw [pow_two]

/-- Pointwise nonnegativity of the reflected diagonal observable kernel. -/
theorem periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal *
        (f x * f x) := by
  rw [periodicHypercubicEvenBoundaryDensity_mul_observable_diagonal_eq_sq]
  exact sq_nonneg _

/-- For a fixed boundary configuration, the orientation-corrected Wilson Gibbs
quadratic integral is the squared norm of the Bochner moment of the weighted
positive-half feature. -/
theorem periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_eq_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hf : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b)
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))) :
    (∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y)
      ∂((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ∂((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))) =
      ‖∫ x,
        periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta f b x
        ∂((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
          (normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin N) ℂ)))‖ ^ 2 := by
  let mu :=
    (periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let g := periodicHypercubicEvenBoundaryObservableGramFeature
    H N hN beta hbeta f b
  change (∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y) ∂mu ∂mu) = ‖∫ x, g x ∂mu‖ ^ 2
  calc
    (∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
          (f x * f y) ∂mu ∂mu) =
        ∫ x, ∫ y, inner ℝ (g x) (g y) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact periodicHypercubicEvenBoundaryDensity_mul_observable_eq_inner
        H N hN beta hbeta f b x y
    _ = ‖∫ x, g x ∂mu‖ ^ 2 := by
      exact iterated_integral_real_inner_eq_norm_integral_sq mu g hf

/-- The corrected boundary-conditioned Wilson quadratic integral is
nonnegative. -/
theorem periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hf : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b)
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))) :
    0 ≤ ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y)
      ∂((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ∂((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ))) := by
  rw [periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_eq_norm_sq
    H N hN beta hbeta f b hf]
  exact sq_nonneg _

end

end MathlibAnalytic
end MGAP4D
