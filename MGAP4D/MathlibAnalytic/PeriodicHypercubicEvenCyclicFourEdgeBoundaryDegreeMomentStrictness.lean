import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisPositiveDegreeWitnessLimit
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureWeightedGramStrictness
import Mathlib.Tactic.FunProp

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

/-- The genuine four-edge degree feature is Bochner integrable against every
bounded normalized-trace polynomial in the actual interacting boundary
marginal.  This is the source-carrier analogue of the existing cyclic target
integrability theorem: the four-edge word is continuous, the edgewise degree
kernel is continuous, and its Hilbert feature has unit norm because every
normalized relative-trace kernel has unit diagonal. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_fourEdgeDegreeFeature_integrable
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ) :
    Integrable
      (fun b =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
            H n).feature b)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta) := by
  let C :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n
  let word := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  have hWord : Continuous word := by
    dsimp [word, periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord]
    fun_prop
  have hCoordinateKernel : ∀ j : Fin 4,
      Continuous fun q :
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
          (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        specialUnitaryNormalizedTraceRelativeKernel 2 (q.1 j) (q.2 j) := by
    intro j
    exact continuous_specialUnitaryNormalizedTraceRelativeKernel_two.comp (by fun_prop)
  have hBaseKernel : Continuous fun q :
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel q.1 q.2 ^ n := by
    simpa [specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel] using
      (((hCoordinateKernel 2).mul (hCoordinateKernel 3)).mul
        ((hCoordinateKernel 0).mul (hCoordinateKernel 1))).pow n
  have hKernel : Continuous fun q :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
        (word q.1) (word q.2) ^ n := by
    exact hBaseKernel.comp
      ((hWord.comp continuous_fst).prod_mk (hWord.comp continuous_snd))
  have hFeature : Continuous C.feature := by
    simpa [C, word,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature] using
      RealHilbertKernelFeature.continuous_feature_of_continuous_kernel C hKernel
  have hRelativeSelf : ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      specialUnitaryNormalizedTraceRelativeKernel 2 g g = 1 := by
    intro g
    unfold specialUnitaryNormalizedTraceRelativeKernel
    rw [show g⁻¹ * g = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) by group]
    exact normalizedSpecialUnitaryRealTrace_one 2
      cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive
  have hFeatureNorm : ∀ b, ‖C.feature b‖ = 1 := by
    intro b
    apply RealHilbertKernelFeature.feature_norm_eq_one
    intro x
    simpa [C, word,
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel,
      hRelativeSelf]
  have hWeighted : Continuous fun b => p b • C.feature b :=
    p.continuous.smul hFeature
  refine Integrable.of_bound hWeighted.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with b
  rw [norm_smul, hFeatureNorm]
  simpa using p.norm_coe_le_norm b

/-- The arbitrary-degree Hilbert-adjoint pullback pairs with the actual four
boundary edges exactly as the original cyclic target dual vector pairs with
the already-constructed boundary degree feature.  This is the source/target
identity needed to move strictness from the interacting cyclic Fock witness to
the genuine edgewise carrier without identifying the two kernels. -/
theorem
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_boundaryFourEdgeDegreeFeature
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
          H n).feature b) =
      inner ℝ q
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H n).feature b) := by
  have h :=
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_feature
      n q (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord,
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy,
    specialUnitaryTwoNormalizedTraceHilbertKernelFeature] using h

/-- A nonzero interacting-boundary cyclic dual pairing forces the Bochner
moment of the genuine four-edge source degree feature to be nonzero.  The
proof is purely the Hilbert-adjoint identity plus `integral_inner`; no marginal
transport-defect hypothesis enters. -/
theorem
    periodicHypercubicEvenBoundaryMarginal_fourEdgeDegreeFeature_integral_ne_zero_of_cyclicDualProbe
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
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n).feature b
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)) ≠ 0 := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta
  let r := specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_fourEdgeDegreeFeature_integrable
        H beta hbeta k c n
  intro hzero
  apply hq
  calc
    (∫ b,
      inner ℝ q
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
            H n).feature b) ∂μ) =
        ∫ b, inner ℝ r (p b • C.feature b) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [real_inner_smul_right, real_inner_smul_right]
      rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_boundaryFourEdgeDegreeFeature]
      rfl
    _ = inner ℝ r (∫ b, p b • C.feature b ∂μ) := integral_inner hIntegrable r
    _ = 0 := by simp [hzero]

/-- The genuine four-edge diagonal degree kernel therefore has a strictly
positive weighted Gram integral whenever it is detected by a nonzero cyclic
dual probe.  This turns the scalar target witness into cancellation-free
source-carrier strict positivity. -/
theorem
    periodicHypercubicEvenBoundaryMarginal_fourEdgeDegreeFeature_weightedGram_pos_of_cyclicDualProbe
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
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₁ •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n).feature b₁)
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₂ •
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n).feature b₂)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta) := by
  let C := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature H n
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_fourEdgeDegreeFeature_integrable
        H beta hbeta k c n
  have hMoment : (∫ b, p b • C.feature b ∂μ) ≠ 0 := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginal_fourEdgeDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta k n c q hq
  simpa [C, p, μ] using
    C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero μ p hIntegrable hMoment

/-- A centered nonzero boundary polynomial at positive coupling produces a
strictly positive genuine four-edge diagonal Fock Gram contribution in some
positive Taylor degree.  The exact physical four-companion coefficient
`(beta^i / i!)^4` is strictly positive and therefore preserves the strictness.

This is the model-specific cancellation-free handoff required before proving
PSD domination by the complete rectangular four-factor Wilson Taylor kernel. -/
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
                (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₁ •
                  (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
                    H (i : ℕ)).feature b₁)
                (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₂ •
                  (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeDegreeFeature
                    H (i : ℕ)).feature b₂)
              ∂(periodicHypercubicEvenBoundaryMarginalMeasure
                H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le)
              ∂(periodicHypercubicEvenBoundaryMarginalMeasure
                H 2 cyclicFourEdgeBoundaryDegreeStrictnessTwoRankPositive beta hbeta.le)) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_dualFeatureProbe
      H beta hbeta k c hc hzero with ⟨i, hi, hcoefficient, q, hq⟩
  refine ⟨i, hi, hcoefficient, q, hq, ?_⟩
  exact mul_pos (pow_pos hcoefficient 4)
    (periodicHypercubicEvenBoundaryMarginal_fourEdgeDegreeFeature_weightedGram_pos_of_cyclicDualProbe
      H beta hbeta.le k (i : ℕ) c q hq)

end

end MathlibAnalytic
end MGAP4D
