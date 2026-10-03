import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityFeatureMoment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeBoundaryDegreeMomentStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureWeightedGramStrictness
import Mathlib.Tactic

/-!
# One-slice cyclic moments force genuine four-edge Gram strictness

The cyclic degree-feature moment from the preceding layer lives in the target
Hilbert carrier of the existing four-edge contraction map.

This file pulls a cyclic dual probe back through the Hilbert adjoint of that
map.  Therefore a nonzero cyclic feature moment forces the genuine edgewise
four-link feature moment to be nonzero on the same one-slice positive-density
measure.  The generic weighted-Gram identity then gives a strictly positive
double integral.

No boundary carrier and no transport-defect hypothesis is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem spatialTraceFourEdgeMomentTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance spatialTraceFourEdgeMomentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance spatialTraceFourEdgeMomentCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance spatialTraceFourEdgeMomentSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance spatialTraceFourEdgeMomentMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance spatialTraceFourEdgeMomentBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance spatialTraceFourEdgeMomentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem continuous_periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord
    (H : ℕ) :
    Continuous (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H) := by
  apply continuous_pi
  intro j
  simpa [periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord] using
    (continuous_apply
      (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j))

private theorem continuous_spatialTraceFourEdgeCoordinateKernel
    (j : Fin 4) :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryNormalizedTraceRelativeKernel 2 (q.1 j) (q.2 j) := by
  exact continuous_specialUnitaryNormalizedTraceRelativeKernel_two.comp₂
    ((continuous_apply j).comp continuous_fst)
    ((continuous_apply j).comp continuous_snd)

private theorem continuous_spatialTraceFourEdgeEdgewiseKernel :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel q.1 q.2 := by
  unfold specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
  exact
    ((continuous_spatialTraceFourEdgeCoordinateKernel 2).mul
      (continuous_spatialTraceFourEdgeCoordinateKernel 3)).mul
      ((continuous_spatialTraceFourEdgeCoordinateKernel 0).mul
        (continuous_spatialTraceFourEdgeCoordinateKernel 1))

/-- Genuine four-edge degree feature evaluated on the four physical links of
the canonical primary spatial plaquette. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature
    (H n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H B) ^ n) :=
  (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).comap
    (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H)

/-- The one-slice genuine four-edge degree feature is continuous. -/
theorem periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature_continuous
    (H n : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature := by
  let C := specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n
  have hKernel : Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel q.1 q.2 ^ n :=
    continuous_spatialTraceFourEdgeEdgewiseKernel.pow n
  have hFeature : Continuous C.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C hKernel
  simpa [C, periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature] using
    hFeature.comp
      (continuous_periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H)

/-- The one-slice genuine four-edge degree feature has unit norm. -/
theorem periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature_norm
    (H n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ‖(periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A‖ = 1 := by
  let C := periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n
  apply RealHilbertKernelFeature.feature_norm_eq_one C
  intro x
  have hSelf : ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      specialUnitaryNormalizedTraceRelativeKernel 2 g g = 1 := by
    intro g
    unfold specialUnitaryNormalizedTraceRelativeKernel
    rw [show g⁻¹ * g = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) by group]
    exact normalizedSpecialUnitaryRealTrace_one 2
      spatialTraceFourEdgeMomentTwoRankPositive
  change
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
      (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H x)
      (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H x) ^ n = 1
  simp only [specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel,
    hSelf, one_mul, one_pow]

/-- Polynomial-weighted genuine four-edge degree features are Bochner
integrable under every finite positive-density change of spatial Haar. -/
theorem periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integrable
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
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  let C := periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n
  have hContinuous : Continuous fun A => p A • C.feature A :=
    p.continuous.smul
      (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature_continuous H n)
  refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with A
  rw [norm_smul]
  have hnorm :
      ‖C.feature A‖ = 1 := by
    simpa [C] using
      periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature_norm H n A
  rw [hnorm]
  simpa [p] using p.norm_coe_le_norm A

/-- The Hilbert-adjoint pullback pairs with the genuine one-slice four-edge
feature exactly as the original cyclic target dual vector pairs with the
one-slice cyclic feature. -/
theorem
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_spatialSliceFourEdgeDegreeFeature
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
        H n).FeatureHilbert)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A) =
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
          H n).feature A) := by
  have h :=
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_feature
      n q (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)
  simpa [
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature,
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature,
    periodicHypercubicEvenPrimarySpatialSliceCyclicHolonomyTwo,
    specialUnitaryTwoNormalizedTraceHilbertKernelFeature] using h

/-- A nonzero cyclic Hilbert feature moment forces the genuine one-slice
four-edge feature moment to be nonzero. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicMoment
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (n : ℕ)
    (hCyclic :
      (∫ A,
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
            H n).feature A
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0) :
    (∫ A,
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0 := by
  let μ :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w
  let T :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature H n
  let S := periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  have hTargetIntegrable : Integrable (fun A => p A • T.feature A) μ := by
    simpa [T, p, μ] using
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integrable
        H k c w n
  rcases
    T.exists_dual_probe_of_integral_ne_zero
      μ (fun A => p A) hTargetIntegrable
      (by simpa [T, p, μ] using hCyclic) with
    ⟨q, hq⟩
  let r := specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q
  have hSourceIntegrable : Integrable (fun A => p A • S.feature A) μ := by
    simpa [S, p, μ] using
      periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integrable
        H k c w n
  intro hzero
  apply hq
  calc
    (∫ A, inner ℝ q (p A • T.feature A) ∂μ) =
        ∫ A, inner ℝ r (p A • S.feature A) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with A
      calc
        inner ℝ q (p A • T.feature A) =
            p A * inner ℝ q (T.feature A) := by
              rw [real_inner_smul_right]
        _ = p A * inner ℝ r (S.feature A) := by
              rw [
                specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_spatialSliceFourEdgeDegreeFeature
                  H n q A]
        _ = inner ℝ r (p A • S.feature A) := by
              change
                p A *
                    inner ℝ r
                      ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).feature
                        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)) =
                  inner ℝ r
                    (p A •
                      (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).feature
                        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A))
              symm
              rw [real_inner_smul_right]
    _ = inner ℝ r (∫ A, p A • S.feature A ∂μ) :=
      integral_inner hSourceIntegrable r
    _ = inner ℝ r 0 := by
      have hzero' : (∫ A, p A • S.feature A ∂μ) = 0 := by
        simpa [S, p, μ] using hzero
      exact congrArg (fun z => inner ℝ r z) hzero'
    _ = 0 := inner_zero_right _

/-- A nonzero cyclic degree moment therefore gives a strictly positive genuine
four-edge weighted Gram double integral on the same one-slice measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_gram_pos_of_cyclicMoment
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (n : ℕ)
    (hCyclic :
      (∫ A,
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
            H n).feature A
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0) :
    0 <
      ∫ A₁, ∫ A₂,
        inner ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₁ •
            (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A₁)
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₂ •
            (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A₂)
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
  let μ :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w
  let C := periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  have hIntegrable : Integrable (fun A => p A • C.feature A) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integrable
        H k c w n
  have hMoment : (∫ A, p A • C.feature A ∂μ) ≠ 0 := by
    simpa [C, p, μ] using
      periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicMoment
        H k c w n hCyclic
  have hGram :=
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
      μ p hIntegrable hMoment
  simpa [C, p, μ] using hGram

/-- Every nonzero finite primary normalized-trace polynomial is detected, under
any equivalent finite positive density, by a strictly positive genuine
four-edge Gram contribution at some strictly positive degree. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_withDensity_exists_positiveDegree_fourEdgeGram_pos
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    (hw :
      AEMeasurable w
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
    (hw_ne_zero :
      ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2),
        w A ≠ 0)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)] :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      0 <
        ∫ A₁, ∫ A₂,
          inner ℝ
            (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₁ •
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature
                H ((i : ℕ) + 1)).feature A₁)
            (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₂ •
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature
                H ((i : ℕ) + 1)).feature A₂)
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
  rcases
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_withDensity_exists_positiveDegree_moment_ne_zero
      H k c hc w hw hw_ne_zero with
    ⟨i, hi, hmoment⟩
  have hCyclic :=
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integral_ne_zero_of_inner_ne_zero
      H k c w ((i : ℕ) + 1) hmoment
  refine ⟨i, hi, ?_⟩
  exact
    periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_gram_pos_of_cyclicMoment
      H k c w ((i : ℕ) + 1) hCyclic

end

end MathlibAnalytic
end MGAP4D
