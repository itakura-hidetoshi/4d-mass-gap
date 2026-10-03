import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightFourEdgeGram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeCrossingSelectedFactorization
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureNonnegSMulMomentStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureWeightedGramStrictness
import Mathlib.Tactic

/-!
# Strict H1-D5 half-weight temporal-crossing Gram at positive coupling

The one-slice trace polynomial has a nonzero positive-degree genuine four-edge
Fock moment under the exact H1-D5 endpoint measure.  At strictly positive
Wilson coupling the corresponding selected one-edge Taylor coefficient is
strictly positive, hence so is its four-edge fourth power.

The exact temporal crossing kernel splits as

  (crossing - protected selected degree) + protected selected degree,

where the first term is Schur positive semidefinite and the second retains both
the literal residual degree-zero factor and the selected four-edge Wilson
sector.  A nonzero selected moment therefore cannot cancel in the direct-sum
Hilbert feature of the full crossing kernel.

The conclusion is strict positivity of the bare temporal-crossing quadratic
form in the same half-weight endpoint measure used by the H1-D5 residual.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

private theorem h1d5CrossingStrictTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance h1d5CrossingStrictTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance h1d5CrossingStrictCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance h1d5CrossingStrictSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance h1d5CrossingStrictMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance h1d5CrossingStrictBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance h1d5CrossingStrictSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The bare temporal crossing kernel has unit diagonal. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_self
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 beta A A = 1 := by
  classical
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_linkSet_prod]
  apply Finset.prod_eq_one
  intro e _he
  exact specialUnitaryWilsonRelativeKernel_self
    2 h1d5CrossingStrictTwoRankPositive beta (A e)

/-- Hilbert feature of the exact Schur-PSD remainder after removing the
protected selected four-edge degree from the bare temporal crossing kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedRemainderFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 beta A B -
          (Real.exp (-beta)) ^
              (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card *
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)
              (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H B)) :=
  (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_sub_residualScalar_mul_primaryFourEdgeSelectedDegreeKernel_positiveSemidefiniteCertificate
    H beta hbeta n).toHilbertFeature

/-- The selected four-edge Wilson degree on the physical one-slice carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeWilsonSelectedDegreeFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H B)) :=
  (specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeFeature beta hbeta n).comap
    (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H)

/-- The fully protected selected degree includes the literal residual
degree-zero scalar from every non-primary spatial link. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
            (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H A)
            (periodicHypercubicEvenPrimarySpatialSliceFourEdgeWord H B)) := by
  let r := (Real.exp (-beta)) ^
    (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card
  let S₀ :=
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeWilsonSelectedDegreeFeature
      H beta hbeta n
  have hr : 0 ≤ r :=
    (periodicHypercubicEvenPrimarySpatialSliceCrossingResidualDegreeZeroScalar_pos
      H beta).le
  simpa [r, S₀] using
    RealHilbertKernelFeature.nonnegSMul r hr S₀

/-- Direct-sum Hilbert realization of the complete bare temporal crossing
kernel with the protected degree retained as the right summand. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :=
  RealHilbertKernelFeature.add
    (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedRemainderFeature
      H beta hbeta n)
    (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature
      H beta hbeta n)

/-- The direct-sum feature inner product is exactly the literal bare temporal
crossing kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_inner_eq_kernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
          H beta hbeta n).feature A)
        ((periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
          H beta hbeta n).feature B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 beta A B := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
      H beta hbeta n
  rw [← C.kernel_eq_inner]
  simp [C,
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature]

/-- The full crossing decomposition feature is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
        H beta hbeta n).feature := by
  apply RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
    (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
      H beta hbeta n)
  simpa [
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature] using
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
      H 2 beta

/-- Every full crossing decomposition feature vector has unit norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_norm
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ‖(periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
        H beta hbeta n).feature A‖ = 1 := by
  apply RealHilbertKernelFeature.feature_norm_eq_one
  intro B
  simpa [
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature] using
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_self H beta B

/-- Polynomial-weighted full crossing feature vectors are Bochner integrable
under every finite positive-density endpoint measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_crossingFullFeature_integrable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
          (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
            H beta hbeta n).feature A)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) := by
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  let C :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
      H beta hbeta n
  have hContinuous : Continuous fun A => p A • C.feature A :=
    p.continuous.smul
      (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_continuous
        H beta hbeta n)
  refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with A
  rw [norm_smul]
  have hnorm : ‖C.feature A‖ = 1 := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_norm
        H beta hbeta n A
  rw [hnorm]
  simpa [p] using p.norm_coe_le_norm A

/-- A nonzero genuine four-edge degree moment remains nonzero after multiplying
by the strictly positive selected Wilson coefficient and the residual
degree-zero scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature_integral_ne_zero_of_fourEdgeMoment
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)]
    (hSource :
      (∫ A,
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
          (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0) :
    (∫ A,
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A •
        (periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature
          H beta hbeta.le n).feature A
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)) ≠ 0 := by
  let μ :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  let C₀ := periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n
  let S₀ :=
    periodicHypercubicEvenPrimarySpatialSliceFourEdgeWilsonSelectedDegreeFeature
      H beta hbeta.le n
  let s := specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n
  let r := (Real.exp (-beta)) ^
    (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card
  have hTaylor : 0 < specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_pos (Real.exp_pos _)
      (div_pos (pow_pos hbeta _) (by positivity))
  have hs : 0 < s := by
    dsimp [s, specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient]
    exact pow_pos hTaylor _
  have hSource' : (∫ A, p A • C₀.feature A ∂μ) ≠ 0 := by
    simpa [μ, p, C₀] using hSource
  have hScaledSelected :
      Real.sqrt s • (∫ A, p A • C₀.feature A ∂μ) ≠ 0 :=
    smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hs)) hSource'
  have hEqSelected :=
    RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
      C₀ μ p s hs.le
  have hSelected : (∫ A, p A • S₀.feature A ∂μ) ≠ 0 := by
    simpa [S₀, C₀, s,
      periodicHypercubicEvenPrimarySpatialSliceFourEdgeWilsonSelectedDegreeFeature,
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeFeature,
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel] using
      hEqSelected.trans_ne hScaledSelected
  have hr : 0 < r :=
    periodicHypercubicEvenPrimarySpatialSliceCrossingResidualDegreeZeroScalar_pos
      H beta
  have hScaledProtected :
      Real.sqrt r • (∫ A, p A • S₀.feature A ∂μ) ≠ 0 :=
    smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hr)) hSelected
  have hEqProtected :=
    RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
      S₀ μ p r hr.le
  simpa [μ, p, S₀, r,
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature]
    using hEqProtected.trans_ne hScaledProtected

/-- At strictly positive coupling every nonzero finite primary trace polynomial
has a positive Fock degree for which the complete bare temporal-crossing
quadratic form is strictly positive in the exact H1-D5 half-weight measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_halfWeightMeasure_exists_positiveDegree_crossingGram_pos
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      0 <
        ∫ A₁, ∫ A₂,
          periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₁ *
            periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c A₂ *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta A₁ A₂
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H 2 beta) := by
  let w :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H 2 beta
  let μ :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  letI hfin : IsFiniteMeasure μ := by
    dsimp [μ, w]
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
        H 2 h1d5CrossingStrictTwoRankPositive beta hbeta.le
  rcases
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_withDensity_exists_positiveDegree_moment_ne_zero
      H k c hc w
      (by
        simpa [w] using
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
            H 2 beta).aemeasurable)
      (Filter.Eventually.of_forall
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_ne_zero
          H 2 beta)) with
    ⟨i, hi, hScalar⟩
  let n := (i : ℕ) + 1
  have hCyclic :
      (∫ A, p A •
        (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceRelativeDegreeFeature
          H n).feature A ∂μ) ≠ 0 := by
    simpa [p, μ, n, w] using
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_degreeFeature_integral_ne_zero_of_inner_ne_zero
        H k c w n hScalar
  have hSource :
      (∫ A, p A •
        (periodicHypercubicEvenPrimarySpatialSliceFourEdgeDegreeFeature H n).feature A
        ∂μ) ≠ 0 := by
    simpa [p, μ, n, w] using
      periodicHypercubicEvenPrimarySpatialSliceWeightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicMoment
        H k c w n
        (by simpa [p, μ, n, w] using hCyclic)
  let R :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedRemainderFeature
      H beta hbeta.le n
  let S :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature
      H beta hbeta.le n
  let C :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature
      H beta hbeta.le n
  have hSelected : (∫ A, p A • S.feature A ∂μ) ≠ 0 := by
    simpa [S, p, μ, n, w] using
      periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingProtectedSelectedDegreeFeature_integral_ne_zero_of_fourEdgeMoment
        H beta hbeta k n c w
        (by simpa [p, μ, n, w] using hSource)
  have hIntegrable : Integrable (fun A => p A • C.feature A) μ := by
    simpa [C, p, μ, w] using
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_crossingFullFeature_integrable
        H beta hbeta.le k c w n
  have hFullMoment : (∫ A, p A • C.feature A ∂μ) ≠ 0 := by
    have hAdd :=
      RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
        R S μ p
        (by
          simpa [C, R, S,
            periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature] using
            hIntegrable)
        hSelected
    simpa [C, R, S,
      periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature] using
      hAdd
  have hGram :
      0 < ∫ A₁, ∫ A₂,
        inner ℝ (p A₁ • C.feature A₁) (p A₂ • C.feature A₂) ∂μ ∂μ :=
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
      μ p hIntegrable hFullMoment
  have hKernel :
      ∀ A₁ A₂,
        inner ℝ (C.feature A₁) (C.feature A₂) =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A₁ A₂ := by
    intro A₁ A₂
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingFullDecompositionFeature_inner_eq_kernel
        H beta hbeta.le n A₁ A₂
  have hWeightedKernel :
      ∀ A₁ A₂,
        inner ℝ (p A₁ • C.feature A₁) (p A₂ • C.feature A₂) =
          p A₁ * p A₂ *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
              H 2 beta A₁ A₂ := by
    intro A₁ A₂
    rw [real_inner_smul_left, real_inner_smul_right, hKernel]
    ring
  have hGramKernel :
      0 < ∫ A₁, ∫ A₂,
        p A₁ * p A₂ *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A₁ A₂ ∂μ ∂μ := by
    simpa only [hWeightedKernel] using hGram
  refine ⟨i, hi, ?_⟩
  simpa [μ, w,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure] using
    hGramKernel

end

end MathlibAnalytic
end MGAP4D
