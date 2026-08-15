import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisOperatorNonzero

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

private theorem boundaryAnalysisApplyRawTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryAnalysisApplyRawNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryAnalysisApplyRawTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryAnalysisApplyRawCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryAnalysisApplyRawSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryAnalysisApplyRawMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryAnalysisApplyRawBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryAnalysisApplyRawSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryAnalysisApplyRawBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance boundaryAnalysisApplyRawOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The explicit continuous raw actual-analysis vector is not merely a test
vector for the canonical Wilson analysis output: it is exactly that output in
open-half Haar `L²`.

The proof uses Riesz uniqueness.  Matrix coefficients of the canonical
Hilbert--Schmidt analysis operator are evaluated by the generic Fubini theorem;
the resulting inner integral is definitionally the explicit raw Wilson
analysis integral.  Thus no surjectivity, density, positivity, or additional
physical-range hypothesis is introduced. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_normalizedTracePolynomial_eq_rawActualAnalysisHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c) =
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta k c := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let ν := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K2 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta
  let f := periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    H beta hbeta k c
  let g := periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
    H beta hbeta k c
  let κ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 → ℝ :=
    fun z => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta z.1 z.2
  let φ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ :=
    fun b =>
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
        periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta b
  let γ : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 → ℝ :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
      H beta hbeta k c
  have hK : K2 =ᵐ[μ.prod ν] κ := by
    simpa [K2, μ, ν, κ] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_actualAnalysis
        H beta hbeta
  have hf0 :
      f =ᵐ[μ]
        fun b =>
          periodicHypercubicEvenBoundaryVacuumMoment
              H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta b *
            periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
              H k c b := by
    simpa [f, μ] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_coeFn
        H beta hbeta k c
  have hf : f =ᵐ[μ] φ := by
    filter_upwards [hf0] with b hb
    rw [hb]
    dsimp [φ]
    ring
  have hg : g =ᵐ[ν] γ := by
    simpa [g, ν, γ] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_coeFn
        H beta hbeta k c
  change
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta f = g
  apply (InnerProductSpace.toDual ℝ (Lp ℝ 2 ν)).injective
  ext q
  change inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 boundaryAnalysisApplyRawTwoRankPositive beta hbeta f) q =
    inner ℝ g q
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner]
  change realL2HilbertSchmidtKernelPairing K2 f q = inner ℝ g q
  calc
    realL2HilbertSchmidtKernelPairing K2 f q =
        ∫ x, ∫ b, inner ℝ (κ (b, x)) (φ b * q x) ∂μ ∂ν := by
      exact
        realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
          K2 f q κ φ (fun x => q x) hK hf
          (Filter.Eventually.of_forall fun _ => rfl)
    _ = ∫ x, inner ℝ (γ x) (q x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        (∫ b, inner ℝ (κ (b, x)) (φ b * q x) ∂μ) =
            ∫ b, (φ b * κ (b, x)) * q x ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with b
          rw [periodicHypercubicEven_real_inner_eq_mul]
          ring
        _ = (∫ b, φ b * κ (b, x) ∂μ) * q x := by
          rw [integral_mul_const]
        _ = γ x * q x := by
          rfl
        _ = inner ℝ (γ x) (q x) := by
          exact (periodicHypercubicEven_real_inner_eq_mul (γ x) (q x)).symm
    _ = ∫ x, inner ℝ (g x) (q x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    _ = inner ℝ g q := by
      exact (MeasureTheory.L2.inner_def g q).symm

end

end MathlibAnalytic
end MGAP4D
