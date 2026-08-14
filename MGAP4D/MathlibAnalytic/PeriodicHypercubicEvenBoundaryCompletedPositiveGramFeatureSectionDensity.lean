import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem boundaryCompletedPositiveGramFeatureSectionDensityTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance boundaryCompletedPositiveGramFeatureSectionDensityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryCompletedPositiveGramFeatureSectionDensityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryCompletedPositiveGramFeatureSectionDensitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryCompletedPositiveGramFeatureSectionDensityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryCompletedPositiveGramFeatureSectionDensityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryCompletedPositiveGramFeatureSectionDensitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual completed-positive scalar Gram feature is strictly positive at
every point of the canonical four-companion section.  This uses the exact
section factorization: the strict-positive bulk amplitude, the literal residual
boundary prefactor, and all four selected Wilson relative kernels are each
strictly positive. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionSection_pos
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 boundaryCompletedPositiveGramFeatureSectionDensityTwoRankPositive
        beta hbeta b
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH) u) := by
  rw [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionSection_eq_openHalfAmplitude_mul_boundaryPrefactor_mul_relativeKernelProduct
      H hH beta hbeta b u]
  have hKernel : ∀ g h : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      0 < specialUnitaryWilsonRelativeKernel 2 beta g h := by
    intro g h
    unfold specialUnitaryWilsonRelativeKernel
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.exp_pos _
  exact mul_pos
    (periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude_pos
      H 2 beta
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH) u))
    (mul_pos
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_pos
        H beta hbeta b)
      (mul_pos
        (mul_pos (hKernel _ _) (hKernel _ _))
        (mul_pos (hKernel _ _) (hKernel _ _))))

/-- For fixed four-companion coordinates, use the actual completed-positive
Gram feature as a pointwise finite positive boundary weight.  Measurability is
deliberately established only at the later theorem that consumes the weight,
so the large finite-lattice dependent type is normalized once rather than in a
standalone declaration. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ≥0∞ :=
  fun b => ENNReal.ofReal
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 boundaryCompletedPositiveGramFeatureSectionDensityTwoRankPositive
      beta hbeta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH) u))

/-- The section density is everywhere nonzero, hence in particular nonzero
boundary-Haar almost everywhere. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity
      H hH beta hbeta u b ≠ 0 := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionSection_pos
    H hH beta hbeta b u

/-- Almost-everywhere nonvanishing receipt in the exact form required by the
positive-density normalized-trace/Fock robustness theorem. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity_ae_ne_zero
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity
        H hH beta hbeta u b ≠ 0 :=
  Filter.Eventually.of_forall fun b =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionDensity_ne_zero
      H hH beta hbeta u b

end

end MathlibAnalytic
end MGAP4D
