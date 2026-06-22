import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousTransport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

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

/-- The completed positive scalar Gram feature is nonnegative. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  apply mul_nonneg (Real.sqrt_nonneg _) ?_
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)

/-- The completed positive scalar Gram feature is exactly the square root of the
orientation-corrected Gibbs density on the reflected diagonal. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      Real.sqrt
        ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal) := by
  let g := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b x
  have hg : 0 ≤ g := by
    dsimp [g]
    exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta b x
  have hdiag :
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal =
        g * g := by
    rw [periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner]
    exact periodicHypercubicEven_real_inner_eq_mul g g
  calc
    g = Real.sqrt (g * g) := (Real.sqrt_mul_self hg).symm
    _ = Real.sqrt
        ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal) := by
      rw [hdiag]

/-- For a fixed boundary configuration, the completed positive Gram feature is
measurable as the square root of the measurable reflected-diagonal density. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Measurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hpair : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x)) :=
    measurable_id.prodMk hc
  have hdiag : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))) :=
    measurable_const.prodMk hpair
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp hdiag)
  simpa only [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity]
    using hsqrt

/-- The completed positive Gram feature is uniformly bounded by the square root
of the reciprocal partition function. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x ≤
      Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity]
  apply Real.sqrt_le_sqrt
  exact
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
      H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))

/-- A bounded continuous positive-half observable produces a measurable scalar
boundary Gram feature. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_measurable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Measurable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b) := by
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  exact
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_measurable
      H N hN beta hbeta b).mul f.continuous.measurable

/-- Sup-norm control of the observable-weighted scalar boundary Gram feature. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x‖ ≤
      Real.sqrt
          (((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
        ‖f‖ := by
  have hg0 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
    H N hN beta hbeta b x
  have hg :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
      H N hN beta hbeta b x
  have hf := f.norm_coe_le_norm x
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hg0]
  exact mul_le_mul hg hf (norm_nonneg _) (Real.sqrt_nonneg _)

/-- For every fixed boundary configuration, a bounded continuous positive-half
observable has an integrable scalar Gram feature. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let bound :=
    Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
      ‖f‖
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hm :=
    periodicHypercubicEvenBoundaryObservableGramFeature_measurable_of_boundedContinuous
      H N hN beta hbeta f b
  exact Integrable.of_bound hm.aestronglyMeasurable bound
    (Filter.Eventually.of_forall fun x =>
      periodicHypercubicEvenBoundaryObservableGramFeature_norm_le_of_boundedContinuous
        H N hN beta hbeta f b x)

/-- Finite-volume Osterwalder--Schrader reflection positivity for every bounded
continuous positive-half observable under the actual even-periodic `SU(N)`
Wilson Gibbs law.  All transport and Gram-feature integrability receipts are
constructed internally. -/
theorem periodicHypercubicEvenWilsonGibbs_reflectionPositive_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ) :
    0 ≤ ∫ A, periodicHypercubicEvenFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  exact periodicHypercubicEvenWilsonGibbs_reflectionPositive
    H N hN beta hbeta f
    (periodicHypercubicEvenWilsonGibbsReflectionTransportData_of_boundedContinuous
      H N hN beta hbeta f)
    (fun b =>
      periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
        H N hN beta hbeta f b)

end

end MathlibAnalytic
end MGAP4D
