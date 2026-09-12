import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2Representative
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelPairingFubini
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

private theorem boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryRawActualAnalysisOperatorNonzeroNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRawActualAnalysisOperatorNonzeroTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRawActualAnalysisOperatorNonzeroCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRawActualAnalysisOperatorNonzeroSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRawActualAnalysisOperatorNonzeroMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRawActualAnalysisOperatorNonzeroBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRawActualAnalysisOperatorNonzeroSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryRawActualAnalysisOperatorNonzeroBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance boundaryRawActualAnalysisOperatorNonzeroOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance boundaryRawActualAnalysisOperatorNonzeroOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The rectangular product-`L²` kernel used by the actual Wilson analysis
operator has the expected completed-positive Gram-feature representative. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_actualAnalysis
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta =ᵐ[
          (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
            (periodicHypercubicEvenOpenHalfHaarMeasure H 2)]
      fun z =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
          beta hbeta z.1 z.2 := by
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta).coeFn_toLp

/-- The raw continuous actual-analysis `L²` vector has the defining raw
integral as its almost-everywhere representative. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_coeFn
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta k c =ᵐ[periodicHypercubicEvenOpenHalfHaarMeasure H 2]
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
        H beta hbeta k c := by
  simpa [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2,
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap] using
    (ContinuousMap.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      (𝕜 := ℝ)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
        H beta hbeta k c))

/-- Pairing the genuine actual Wilson analysis output with its explicit raw
continuous representative gives exactly the squared `L²` norm of that raw
representative.  The proof passes through the generic Hilbert--Schmidt Fubini
formula and the already-proved square-root-density representative of the
existing boundary Haar input. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner_rawActualAnalysisHaarL2_eq_norm_sq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c))
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
          H beta hbeta k c) =
      ‖periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
          H beta hbeta k c‖ ^ 2 := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let ν := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K2 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    H beta hbeta k c
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    H beta hbeta k c
  let κ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 → ℝ :=
    fun z => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta z.1 z.2
  let φ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
    fun b =>
      periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta b *
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b
  let γ : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 → ℝ :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
      H beta hbeta k c
  have hK : K2 =ᵐ[μ.prod ν] κ := by
    simpa [K2, μ, ν, κ] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_actualAnalysis
        H beta hbeta
  have hf : f =ᵐ[μ] φ := by
    simpa [f, μ, φ] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_coeFn
        H beta hbeta k c
  have hg : g =ᵐ[ν] γ := by
    simpa [g, ν, γ] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_coeFn
        H beta hbeta k c
  calc
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing K2 f g := by
        simpa [K2, f, g] using
          periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
            H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
            beta hbeta f g
    _ = ∫ x, ∫ b, inner ℝ (κ (b, x)) (φ b * γ x) ∂μ ∂ν :=
      realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
        K2 f g κ φ γ hK hf hg
    _ = ∫ x, γ x * γ x ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hinner :
          (∫ b, inner ℝ (κ (b, x)) (φ b * γ x) ∂μ) =
            γ x * γ x := by
        calc
          (∫ b, inner ℝ (κ (b, x)) (φ b * γ x) ∂μ) =
              ∫ b, ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
                    H k c b *
                  periodicHypercubicEvenBoundaryVacuumMoment
                    H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
                    beta hbeta b) *
                periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                  H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
                  beta hbeta b x) * γ x ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with b
            rw [periodicHypercubicEven_real_inner_eq_mul]
            dsimp [κ, φ]
            ring
          _ = (∫ b,
                (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
                    H k c b *
                  periodicHypercubicEvenBoundaryVacuumMoment
                    H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
                    beta hbeta b) *
                periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                  H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive
                  beta hbeta b x ∂μ) * γ x := by
            rw [integral_mul_const]
          _ = γ x * γ x := by
            rfl
      exact hinner
    _ = inner ℝ g g := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
      exact (periodicHypercubicEven_real_inner_eq_mul (γ x) (γ x)).symm
    _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g

/-- Every nonzero normalized-trace polynomial has genuinely nonzero output
under the actual completed-positive Wilson boundary analysis operator.  The
positive-degree four-edge transform supplies a nonzero raw `L²` test vector,
and its exact matrix coefficient against the actual output is its positive
squared norm. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_normalizedTracePolynomial_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta.le
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta.le k c) ≠ 0 := by
  rcases
    periodicHypercubicEvenNormalizedTracePolynomial_exists_positiveDegree_rawActualAnalysisHaarL2_ne_zero
      H hH beta hbeta k c hc with
    ⟨_i, _hi, hg⟩
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    H beta hbeta.le k c
  have hg' : g ≠ 0 := by
    simpa [g] using hg
  have hpair :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner_rawActualAnalysisHaarL2_eq_norm_sq
      H beta hbeta.le k c
  have hpos :
      0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta.le
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta.le k c)) g := by
    rw [hpair]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg')
  intro hzero
  rw [hzero] at hpos
  simp at hpos

/-- The preceding nonzero analysis output is exactly a strict witness for the
canonical factorized operator `A†A`. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_normalizedTracePolynomial_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta.le
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta.le k c))
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        H beta hbeta.le k c) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_normalizedTracePolynomial_ne_zero
        H hH beta hbeta k c hc))

/-- A centered nonzero normalized-trace polynomial therefore produces a genuine
nonzero actual Wilson open-half output orthogonal to the vacuum.  This is the
actual-analysis nonzero bridge needed downstream; no protected-sector lower
bound or sign choice remains in this Hilbert-space step. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered_and_ne_zero_of_normalizedTracePolynomial_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta.le)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta.le k c) = 0) :
    inner ℝ
        (periodicHypercubicEvenOpenHalfConstantOneL2 H 2)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta.le
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta.le k c)) = 0 ∧
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 boundaryRawActualAnalysisOperatorNonzeroTwoRankPositive beta hbeta.le
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta.le k c) ≠ 0 := by
  exact
    periodicHypercubicEvenBoundaryNormalizedTracePolynomial_actualAnalysisOutput_centered_and_ne_zero_of_factorized_inner_self_pos
      H beta hbeta.le k c hzero
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_of_normalizedTracePolynomial_ne_zero
        H hH beta hbeta k c hc)

end

end MathlibAnalytic
end MGAP4D
