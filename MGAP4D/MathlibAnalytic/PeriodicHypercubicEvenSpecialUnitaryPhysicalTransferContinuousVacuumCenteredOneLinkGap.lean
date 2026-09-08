import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumUniformDoobFactor
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumCenteredOneLinkGapSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- On a probability space, a square-integrable centered real observable has
extended variance exactly equal to its squared residual from the zero constant.

This is the Hilbert-space content of the exact spectral-gap-one statement for
complete heat-bath resampling of a single fiber: the heat-bath operator is the
orthogonal projection onto constants, so on the centered fiber its residual
energy is the full squared norm. -/
theorem evariance_eq_doobCenteredSquaredResidual_zero_of_integral_eq_zero
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (X : α → ℝ)
    (hX : MemLp X 2 μ)
    (hmean : ∫ x, X x ∂μ = 0) :
    evariance X μ = doobCenteredSquaredResidual μ X 0 := by
  rw [evariance_eq_lintegral_ofReal]
  simp [doobCenteredSquaredResidual, hmean]

/-- The literal full four-dimensional Wilson one-link conditional law has
exact centered heat-bath spectral gap one.  No compact-group Laplacian estimate
is required: exact one-link resampling is projection onto the constants of that
conditional probability fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLink_centered_evariance_eq_zeroResidual
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)))
    (hmean :
      ∫ g, X g ∂
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) = 0) :
    evariance X
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) =
      doobCenteredSquaredResidual
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) X 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  have hprob : IsProbabilityMeasure (C.singleLinkConditionalMeasure A fullTarget) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A fullTarget
  exact
    @evariance_eq_doobCenteredSquaredResidual_zero_of_integral_eq_zero
      _ _ (C.singleLinkConditionalMeasure A fullTarget) hprob X
      (by simpa [C, fullTarget] using hX)
      (by simpa [C, fullTarget] using hmean)

/-- Explicit volume-uniform physical one-link coercivity on the centered fiber.
The raw Wilson heat-bath gap is exactly one, while the canonical continuous
physical-vacuum Doob transform loses only the Harnack factor `exp (-16 * beta)`.
The coefficient is independent of the base configuration and of the lattice
side length `H`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_centered_zeroResidual_exp_neg_sixteen_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)))
    (hmean :
      ∫ g, X g ∂
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) = 0) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
        doobCenteredSquaredResidual
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
              A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) X 0 ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
          H N hN beta hbeta A target) := by
  rw [← periodicHypercubicEvenSpecialUnitaryWilsonFullSpatialLink_centered_evariance_eq_zeroResidual
    H N hN beta hbeta A target X hX hmean]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_evariance_exp_neg_sixteen_lower_bound
      H N hN beta hbeta A target X hX

end

end MathlibAnalytic
end MGAP4D
