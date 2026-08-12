import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisPositiveDegreeWitnessLimit
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureWeightedGramStrictness

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeBoundaryDegreeStrictnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeBoundaryDegreeStrictnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeBoundaryDegreeStrictnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeBoundaryDegreeStrictnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeBoundaryDegreeStrictnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeBoundaryDegreeStrictnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem continuous_cyclicFourEdgeBoundaryWord
    (H : ℕ) :
    Continuous (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H) := by
  apply continuous_pi
  intro j
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord] using
    (continuous_apply
      (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H j))

private theorem continuous_cyclicFourEdgeCoordinateKernel
    (j : Fin 4) :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryNormalizedTraceRelativeKernel 2 (q.1 j) (q.2 j) := by
  exact continuous_specialUnitaryNormalizedTraceRelativeKernel_two.comp₂
    ((continuous_apply j).comp continuous_fst)
    ((continuous_apply j).comp continuous_snd)

private theorem continuous_cyclicFourEdgeEdgewiseKernel :
    Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel q.1 q.2 := by
  unfold specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
  exact
    ((continuous_cyclicFourEdgeCoordinateKernel 2).mul
      (continuous_cyclicFourEdgeCoordinateKernel 3)).mul
      ((continuous_cyclicFourEdgeCoordinateKernel 0).mul
        (continuous_cyclicFourEdgeCoordinateKernel 1))

/-- The genuine source degree feature evaluated on the four fixed boundary edges. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue
    (H n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert :=
  (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).feature
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)

/-- The boundary polynomial weighted genuine source degree feature. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
    (H k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert :=
  periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b

/-- The genuine source degree feature is continuous on the actual boundary carrier. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_continuous
    (H n : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n) := by
  let C := specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n
  have hKernel : Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel q.1 q.2 ^ n :=
    continuous_cyclicFourEdgeEdgewiseKernel.pow n
  have hFeature : Continuous C.feature :=
    RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C hKernel
  simpa [C, periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
    hFeature.comp (continuous_cyclicFourEdgeBoundaryWord H)

/-- The genuine source degree feature has unit norm. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_norm
    (H n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    ‖periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b‖ = 1 := by
  let C := specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n
  change ‖C.feature (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)‖ = 1
  apply RealHilbertKernelFeature.feature_norm_eq_one C
  intro x
  have hSelf : ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      specialUnitaryNormalizedTraceRelativeKernel 2 g g = 1 := by
    intro g
    unfold specialUnitaryNormalizedTraceRelativeKernel
    rw [show g⁻¹ * g = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) by group]
    exact normalizedSpecialUnitaryRealTrace_one 2
      cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive
  simp only [specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel,
    hSelf, one_mul, one_pow]

/-- Bounded polynomial weights make every genuine four-edge source degree feature
Bochner integrable in the interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature_integrable
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ) :
    Integrable
      (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta) := by
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  have hContinuous : Continuous
      (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n) := by
    simpa [periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature, p] using
      p.continuous.smul
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_continuous H n)
  refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with b
  rw [periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature,
    norm_smul,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue_norm]
  simpa [p] using p.norm_coe_le_norm b

/-- The Hilbert adjoint pullback pairs with the genuine four-edge source feature
exactly as the original cyclic target dual vector pairs with the cyclic target feature. -/
theorem
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_boundaryFourEdgeDegreeFeatureValue
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b) =
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b) := by
  have h :=
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_feature
      n q (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord,
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy,
    specialUnitaryTwoNormalizedTraceHilbertKernelFeature] using h

/-- A nonzero cyclic dual pairing forces the genuine four-edge source Bochner
moment to be nonzero, without any marginal transport-defect assumption. -/
theorem
    periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicDualProbe
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (hq :
      (∫ b,
        inner ℝ q
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H n).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)) ≠ 0) :
    (∫ b,
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)) ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta
  let r := specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q
  have hIntegrable : Integrable
      (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n) μ := by
    simpa [μ] using
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature_integrable
        H beta hbeta k c n
  intro hzero
  apply hq
  calc
    (∫ b,
      inner ℝ q
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
            H n).feature b) ∂μ) =
        ∫ b, inner ℝ r
          (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with b
      calc
        inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H n).feature b) =
            periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
              inner ℝ q
                ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                  H n).feature b) := by rw [real_inner_smul_right]
        _ = periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
              inner ℝ r
                (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b) := by
            rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_boundaryFourEdgeDegreeFeatureValue]
        _ = inner ℝ r
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
                periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue H n b) := by
            symm
            rw [real_inner_smul_right]
        _ = inner ℝ r
              (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b) := rfl
    _ = inner ℝ r
        (∫ b, periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b ∂μ) :=
      integral_inner hIntegrable r
    _ = 0 := by
      calc
        inner ℝ r
            (∫ b, periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b ∂μ) =
            inner ℝ r 0 := congrArg (fun z => inner ℝ r z) hzero
        _ = 0 := by
          rw [← zero_smul ℝ r, real_inner_smul_right, zero_mul]

/-- The selected genuine four-edge diagonal degree has a strictly positive
weighted Gram integral whenever it is detected by a cyclic dual probe. -/
theorem
    periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_gram_pos_of_cyclicDualProbe
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (hq :
      (∫ b,
        inner ℝ q
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H n).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)) ≠ 0) :
    0 < ∫ b₁, ∫ b₂,
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₁)
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₂)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta) := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, p, μ,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature_integrable
        H beta hbeta k c n
  have hMoment : (∫ b, p b • C.feature b ∂μ) ≠ 0 := by
    simpa [C, p, μ,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
      periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using
      periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta k n c q hq
  have hGram :=
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero μ p hIntegrable hMoment
  simpa [C, p, μ,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
    periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeatureValue] using hGram

/-- A centered nonzero boundary polynomial at positive coupling has a strictly
positive genuine four-edge diagonal Fock contribution in some positive Taylor degree. -/
theorem
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_fourEdgeDiagonalGram_strict
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le)) ≠ 0 ∧
        0 <
          (beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ)) ^ 4 *
            (∫ b₁, ∫ b₂,
              inner ℝ
                (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
                  H k c (i : ℕ) b₁)
                (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
                  H k c (i : ℕ) b₂)
              ∂(periodicHypercubicEvenBoundaryMarginalMeasure
                H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le)
              ∂(periodicHypercubicEvenBoundaryMarginalMeasure
                H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le)) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_dualFeatureProbe
      H beta hbeta k c hc hzero with ⟨i, hi, hcoefficient, q, hq⟩
  refine ⟨i, hi, hcoefficient, q, hq, ?_⟩
  exact mul_pos (pow_pos hcoefficient 4)
    (periodicHypercubicEvenBoundaryMarginal_weightedFourEdgeDegreeFeature_gram_pos_of_cyclicDualProbe
      H beta hbeta.le k (i : ℕ) c q hq)

end

end MathlibAnalytic
end MGAP4D
