import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityMoment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeNormalizedTraceHilbertPowerPullback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockFeatureMoment
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureKernelMomentNonzero
import Mathlib.Tactic

/-!
# One-slice primary trace moments lift to cyclic Hilbert feature moments

The remaining H1-D5 problem already lives on one physical spatial slice with an
equivalent positive density.  The preceding scalar theorem produces a nonzero
pairing with a positive normalized-trace power.

This file lifts that scalar witness to the canonical Hilbert tensor feature of
the normalized relative-trace kernel, still on the same one-slice carrier.

The cyclic plaquette word is used because the existing four-edge Fock map
lands in exactly that Hilbert carrier.  The natural oriented plaquette word and
the cyclic word are conjugate, so their normalized traces coincide.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem spatialTraceFeatureMomentTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance spatialTraceFeatureMomentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance spatialTraceFeatureMomentCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance spatialTraceFeatureMomentSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance spatialTraceFeatureMomentMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance spatialTraceFeatureMomentBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance spatialTraceFeatureMomentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance spatialTraceFeatureMomentHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance spatialTraceFeatureMomentSpatialHaarFinite (H : ℕ) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance spatialTraceFeatureMomentSpatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The four physical edge values of the canonical primary spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun k => A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k)

/-- The cyclic representative of the canonical primary spatial plaquette on a
single spatial slice. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  haarFinFourCyclicPlaquetteWord
    (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)

/-- The one-slice cyclic holonomy depends continuously on the spatial links. -/
theorem continuous_periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo
    (H : ℕ) :
    Continuous (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H) := by
  unfold periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo
  unfold periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord
  unfold haarFinFourCyclicPlaquetteWord
  unfold haarFinFourCyclicNestedCoordinates
  unfold haarCyclicPlaquetteWord
  fun_prop

/-- The normalized trace of the cyclic representative equals the normalized
trace of the naturally oriented physical plaquette. -/
theorem periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_eq_cyclic
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A =
      normalizedSpecialUnitaryRealTrace 2
        (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H A) := by
  rw [periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_apply]
  rw [periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge]
  rw [orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord]
  exact
    normalizedSpecialUnitaryRealTrace_conjInvariant
      ((periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A) 0 *
        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A) 1)
      (haarFinFourCyclicPlaquetteWord
        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A))

/-- Canonical identity-link spatial configuration, used as the kernel
basepoint. -/
noncomputable def periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint
    (H : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun _ => 1

@[simp] theorem periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo_basepoint
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H
        (periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint H) =
      1 := by
  simp [periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo,
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord,
    periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint,
    haarFinFourCyclicPlaquetteWord,
    haarFinFourCyclicNestedCoordinates_apply,
    haarCyclicPlaquetteWord]

/-- Degree-n cyclic normalized-relative-trace feature on one spatial slice. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
    (H n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        specialUnitaryNormalizedTraceRelativeKernel 2
          (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H A)
          (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H B) ^ n) :=
  ((specialUnitaryNormalizedTraceRelativeKernelFeature
      2 spatialTraceFeatureMomentTwoRankPositive).pow n).comap
    (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H)

/-- At the identity-link basepoint, the cyclic relative-trace kernel is exactly
the primary plaquette normalized trace. -/
theorem periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeKernel_basepoint
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    specialUnitaryNormalizedTraceRelativeKernel 2
        (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H
          (periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint H))
        (periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H A) =
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A := by
  rw [periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo_basepoint]
  simp only [specialUnitaryNormalizedTraceRelativeKernel, inv_one, one_mul]
  exact
    (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous_eq_cyclic
      H A).symm

/-- Polynomial-weighted one-slice cyclic degree features are Bochner
integrable under every finite positive-density change of spatial Haar. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integrable
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (n : ℕ) :
    Integrable
      (fun A =>
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
            H n).feature A)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
  let C₀ :=
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 spatialTraceFeatureMomentTwoRankPositive).pow n
  let C :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature H n
  let hol := periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  have hBaseKernel : Continuous fun q :
      Matrix.specialUnitaryGroup (Fin 2) ℂ ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      specialUnitaryNormalizedTraceRelativeKernel 2 q.1 q.2 ^ n :=
    continuous_specialUnitaryNormalizedTraceRelativeKernel_two.pow n
  have hBaseFeature : Continuous C₀.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C₀ hBaseKernel
  have hhol : Continuous hol :=
    continuous_periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H
  have hFeature : Continuous C.feature := by
    simpa [C, C₀, hol,
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature] using
      hBaseFeature.comp hhol
  have hWeighted : Continuous fun A => p A • C.feature A :=
    p.continuous.smul hFeature
  have hFeatureNorm : ∀ A, ‖C.feature A‖ = 1 := by
    intro A
    apply RealHilbertKernelFeature.feature_norm_eq_one
    intro x
    simp [C,
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature,
      specialUnitaryNormalizedTraceRelativeKernel_self
        2 spatialTraceFeatureMomentTwoRankPositive]
  refine Integrable.of_bound hWeighted.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with A
  rw [norm_smul, hFeatureNorm]
  simpa using p.norm_coe_le_norm A

/-- A nonzero scalar normalized-trace power pairing forces the corresponding
one-slice cyclic tensor-feature Bochner moment to be nonzero. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integral_ne_zero_of_inner_ne_zero
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (n : ℕ)
    (hmoment :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^ n))
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c)) ≠ 0) :
    (∫ A,
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
        (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
          H n).feature A
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0 := by
  let C :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature H n
  let hol := periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo H
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  let μ :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w
  have hInnerEq :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 μ ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^ n))
        (ContinuousMap.toLp (E := ℝ) 2 μ ℝ p) =
      ∫ A, p A *
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A ^ n
        ∂μ := by
    simpa using MeasureTheory.ContinuousMap.inner_toLp μ
      (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^ n) p
  have hTraceMoment :
      (∫ A, p A *
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A ^ n
        ∂μ) ≠ 0 := by
    intro hz
    apply hmoment
    simpa [μ, p] using hInnerEq.trans hz
  have hSection : ∀ A,
      specialUnitaryNormalizedTraceRelativeKernel 2
        (hol (periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint H))
        (hol A) =
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H A := by
    intro A
    simpa [hol] using
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeKernel_basepoint
        H A
  have hKernelMoment :
      (∫ A, p A *
        specialUnitaryNormalizedTraceRelativeKernel 2
          (hol (periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint H))
          (hol A) ^ n
        ∂μ) ≠ 0 := by
    simpa only [hSection] using hTraceMoment
  have hIntegrable : Integrable (fun A => p A • C.feature A) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integrable
        H k c w n
  have hNonzero :=
    C.integral_ne_zero_of_kernel_moment_ne_zero
      μ (fun A => p A) hIntegrable
      (periodicHypercubicEvenPrimarySpatialSliceTraceKernelBasepoint H)
      hKernelMoment
  simpa [C, hol, p, μ,
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature]
    using hNonzero

end

end MathlibAnalytic
end MGAP4D
