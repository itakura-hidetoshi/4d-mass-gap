import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryEffectiveSectionDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem boundaryEffectiveSectionAnalysisValueTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryEffectiveSectionAnalysisValueNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryEffectiveSectionAnalysisValueTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryEffectiveSectionAnalysisValueCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryEffectiveSectionAnalysisValueSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryEffectiveSectionAnalysisValueMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryEffectiveSectionAnalysisValueBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryEffectiveSectionAnalysisValueSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Explicit Haar-side representative of the actual completed-positive Wilson
analysis output for the normalized-trace polynomial after square-root vacuum
transport.  This is deliberately a pointwise real function; the `L²` quotient
identification is kept for a later bridge. -/
noncomputable def periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  ∫ b,
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
      periodicHypercubicEvenBoundaryVacuumMoment
        H 2 boundaryEffectiveSectionAnalysisValueTwoRankPositive beta hbeta b) *
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 boundaryEffectiveSectionAnalysisValueTwoRankPositive beta hbeta b x
    ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)

/-- On the canonical section determined by a boundary four-edge word, the
actual completed-positive Gram feature is the strictly-positive open-half
amplitude times the complete boundary prefactor times the exact four-edge
Wilson product kernel. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionBoundaryWord_eq_openHalfAmplitude_mul_boundaryPrefactor_mul_exactFourEdgeWilsonProductKernel
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 boundaryEffectiveSectionAnalysisValueTwoRankPositive beta hbeta b
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) *
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
            H beta hbeta b *
          specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) := by
  rw [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionSection_eq_openHalfAmplitude_mul_boundaryPrefactor_mul_relativeKernelProduct
      H hH beta hbeta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)]
  rfl

/-- The exact four-edge transform under the effective density is exactly the
boundary-Haar integral with the real effective weight `ψ_boundary * ρ_boundary`.
No interaction factor is removed. -/
theorem periodicHypercubicEvenBoundaryEffectiveSectionDensity_integral_eq_boundaryHaar
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    (∫ b,
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
        specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity
        (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta))) =
      ∫ b,
        periodicHypercubicEvenBoundaryEffectiveSectionRealWeight H beta hbeta b *
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
            specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d))
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  have htop :
      ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
        periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta b < ⊤ :=
    Filter.Eventually.of_forall fun b => by
      unfold periodicHypercubicEvenBoundaryEffectiveSectionDensity
      exact ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (periodicHypercubicEvenBoundaryEffectiveSectionDensity_measurable
      H beta hbeta).aemeasurable htop]
  apply integral_congr_ae
  filter_upwards [] with b
  unfold periodicHypercubicEvenBoundaryEffectiveSectionDensity
  rw [ENNReal.toReal_ofReal
    (periodicHypercubicEvenBoundaryEffectiveSectionRealWeight_pos H beta hbeta b).le]
  simp only [smul_eq_mul]

/-- The explicit raw actual-analysis value on a canonical four-companion
section is the strictly-positive open-half amplitude times the exact transform
under the effective positive boundary density. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis_fourCompanionBoundaryWord_eq_openHalfAmplitude_mul_effectiveTransform
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
        H beta hbeta k c
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) *
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
            specialUnitaryTwoCyclicFourEdgeWilsonProductKernel beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)
          ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity
            (periodicHypercubicEvenBoundaryEffectiveSectionDensity H beta hbeta))) := by
  rw [periodicHypercubicEvenBoundaryEffectiveSectionDensity_integral_eq_boundaryHaar]
  unfold periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionBoundaryWord_eq_openHalfAmplitude_mul_boundaryPrefactor_mul_exactFourEdgeWilsonProductKernel
      H hH beta hbeta b d]
  unfold periodicHypercubicEvenBoundaryEffectiveSectionRealWeight
  ring

/-- A nonzero normalized-trace polynomial therefore has a concrete canonical
open-half section where the explicit actual Wilson analysis representative is
nonzero.  The witness comes from the exact four-edge transform and the
strictly-positive bulk Wilson amplitude. -/
theorem
    periodicHypercubicEvenNormalizedTracePolynomial_exists_positiveDegree_rawActualAnalysis_fourCompanionSection_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0) :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      ∃ d : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2,
        periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis
            H beta hbeta.le k c
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
              H (Nat.zero_lt_of_lt hH)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d)) ≠ 0 := by
  rcases
    periodicHypercubicEvenNormalizedTracePolynomial_effectiveSectionDensity_exists_positiveDegree_exactFourEdgeWilsonTransform_ne_zero
      H beta hbeta k c hc with
    ⟨i, hi, d, hd⟩
  refine ⟨i, hi, d, ?_⟩
  rw [
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis_fourCompanionBoundaryWord_eq_openHalfAmplitude_mul_effectiveTransform
      H hH beta hbeta.le k c d]
  exact mul_ne_zero
    (ne_of_gt
      (periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude_pos
        H 2 beta
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H d))))
    hd

end

end MathlibAnalytic
end MGAP4D
