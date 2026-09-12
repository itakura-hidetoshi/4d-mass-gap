import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureTemporalFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonSectionFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private theorem boundaryCompletedPositiveGramFeatureSectionFactorizationTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance boundaryCompletedPositiveGramFeatureSectionFactorizationSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- On the canonical four-companion section, the literal product of **all**
positive-boundary temporal Wilson relative kernels separates into the exact
residual boundary factor and the four selected companion kernels.

No residual plaquette is deleted: every residual kernel remains in the first
finite product, with its open-path argument identified geometrically with the
identity. -/
theorem
    periodicHypercubicEvenPositiveBoundaryTemporalFullRelativeKernelProduct_fourCompanionSection_eq_residualBoundaryProduct_mul_relativeKernelProduct
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
      specialUnitaryWilsonRelativeKernel 2 beta
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) u) p)) =
      (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
          1) *
      ((specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 2) (u 2) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 3) (u 3)) *
       (specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 0) (u 0) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 1) (u 1))) := by
  rw [←
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_boundaryFibered_eq_relativeKernelProduct
      (Nat.zero_lt_of_lt hH) beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH) u)
      (fun _ => 1)]
  exact
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_fourCompanionSection_eq_residualBoundaryProduct_mul_relativeKernelProduct
      H hH beta b u (fun _ => 1)

/-- Strictly-positive boundary factor that remains after restricting the actual
completed-positive Gram feature to the canonical four-companion section.
It contains both the physical boundary square-root coefficient and every
literal residual positive-boundary temporal Wilson kernel. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  Real.sqrt
      (periodicHypercubicEvenBoundaryGramCoefficient H 2
        boundaryCompletedPositiveGramFeatureSectionFactorizationTwoRankPositive
        beta hbeta b) *
    ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
      specialUnitaryWilsonRelativeKernel 2 beta
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
        1

/-- The section boundary prefactor is pointwise strictly positive.  The proof
uses only positivity of the physical boundary square-root coefficient and of
each exact Wilson Boltzmann exponential. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor_pos
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    0 < periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
      H beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
  apply mul_pos
  · exact periodicHypercubicEvenBoundaryGramCoefficient_sqrt_pos
      H 2 boundaryCompletedPositiveGramFeatureSectionFactorizationTwoRankPositive
      beta hbeta b
  · apply Finset.prod_pos
    intro p hp
    unfold specialUnitaryWilsonRelativeKernel
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.exp_pos _

/-- Exact section factorization of the **actual completed-positive scalar Gram
feature**.  On the four selected physical open-path coordinates it is a
strictly-positive open-half bulk scalar times a strictly-positive boundary
prefactor times the four explicit relative Wilson kernels.

This is the direct interface from the literal finite-volume Wilson geometry to
the actual Hilbert--Schmidt analysis kernel. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_fourCompanionSection_eq_openHalfAmplitude_mul_boundaryPrefactor_mul_relativeKernelProduct
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 boundaryCompletedPositiveGramFeatureSectionFactorizationTwoRankPositive
        beta hbeta b
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH) u) =
      periodicHypercubicEvenPositiveWilsonOpenHalfAmplitude H 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) u) *
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
            H beta hbeta b *
          ((specialUnitaryWilsonRelativeKernel 2 beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 2) (u 2) *
            specialUnitaryWilsonRelativeKernel 2 beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 3) (u 3)) *
           (specialUnitaryWilsonRelativeKernel 2 beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 0) (u 0) *
            specialUnitaryWilsonRelativeKernel 2 beta
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 1) (u 1)))) := by
  rw [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_openHalf_mul_boundarySqrt_mul_fullTemporalKernelProduct
      (Nat.zero_lt_of_lt hH)
      boundaryCompletedPositiveGramFeatureSectionFactorizationTwoRankPositive
      beta hbeta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH) u)]
  rw [
    periodicHypercubicEvenPositiveBoundaryTemporalFullRelativeKernelProduct_fourCompanionSection_eq_residualBoundaryProduct_mul_relativeKernelProduct
      H hH beta b u]
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureSectionBoundaryPrefactor
  ring

end

end MathlibAnalytic
end MGAP4D
