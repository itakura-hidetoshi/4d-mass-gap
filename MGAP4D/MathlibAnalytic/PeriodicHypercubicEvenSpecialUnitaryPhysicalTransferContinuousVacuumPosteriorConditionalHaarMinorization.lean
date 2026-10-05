import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSingleLinkConditional
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack
import Mathlib.Tactic

/-!
# Uniform Haar minorization for posterior one-link conditionals

The continuous-vacuum posterior one-link conditional density is the normalized
complete ground-state target-fiber weight

  W(g) = K(left, right[target := g]) * Omega(right[target := g]).

The one-slab kernel and the canonical continuous vacuum each satisfy the same
volume-independent one-link Harnack comparison with factor exp(8 beta).
Therefore the complete weight satisfies the pairwise comparison

  W(g) <= exp(16 beta) * W(h).

After Haar normalization this implies the pointwise density floor

  exp(-16 beta) <= p(g).

Consequently every posterior one-link conditional expectation dominates an
exp(-16 beta) fraction of normalized Haar for every nonnegative continuous
test.  This is a genuine volume-independent Doeblin ingredient.  It does not
yet compose a full sweep and makes no strict Dobrushin, infinite-volume,
Euclidean-time, H1-D5, or complete Yang--Mills mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorConditionalMinorizationTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorConditionalMinorizationCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorConditionalMinorizationSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorConditionalMinorizationMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorConditionalMinorizationBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The complete continuous-ground-state target-fiber weight has a
volume-independent pairwise Harnack ratio exp(16 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_le_exp_sixteen_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target g <=
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right target h := by
  let rightg :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N right target g
  let righth :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N right target h
  let R : ℝ := Real.exp (8 * beta)
  have hKernel :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left rightg <=
        R *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left righth := by
    simpa [R, rightg, righth,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta left right target g h
  have hVacuum :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta rightg <=
        R *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta righth := by
    simpa [R, rightg, righth] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta right target g h
  have hVacuumNonneg :
      0 <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta rightg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta rightg).le
  have hScaledKernelNonneg :
      0 <=
        R *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left righth :=
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta left righth).le
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left rightg *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta rightg <=
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left righth *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta righth)
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left rightg *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta rightg <=
      (R *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left righth) *
        (R *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta righth) :=
      mul_le_mul hKernel hVacuum hVacuumNonneg hScaledKernelNonneg
    _ =
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left righth *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta righth) := by
      dsimp [R]
      rw [← Real.exp_add]
      ring_nf

/-- The posterior one-link conditional density has the uniform pointwise floor
exp(-16 beta), independently of the lattice volume and environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_exp_neg_sixteen_mul_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta B A target g := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H N hN beta hbeta B A target
  let logW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H N hN beta hbeta B A target
  have hWContinuous : Continuous W := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_continuous
        H N hN beta hbeta B A target
  have hWInt : Integrable W μ :=
    hWContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZPos : 0 < ∫ h, W h ∂μ := by
    have hPartition :=
      continuousExpPartition_pos μ logW
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_continuous
          H N hN beta hbeta B A target)
    unfold continuousExpPartition at hPartition
    simpa [W, logW] using hPartition
  have hZUpper :
      (∫ h, W h ∂μ) <= Real.exp (16 * beta) * W g := by
    have hConstInt : Integrable (fun _h :
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Real.exp (16 * beta) * W g) μ :=
      integrable_const _
    calc
      (∫ h, W h ∂μ) <=
          ∫ _h : Matrix.specialUnitaryGroup (Fin N) ℂ,
            Real.exp (16 * beta) * W g ∂μ := by
        apply integral_mono hWInt hConstInt
        intro h
        simpa [W] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_le_exp_sixteen_mul
            H N hN beta hbeta B A target h g
      _ = Real.exp (16 * beta) * W g := by simp
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_eq_groundStateNormalizedDensity,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_eq]
  change
    Real.exp (-16 * beta) <= W g / ∫ h, W h ∂μ
  apply (le_div_iff₀ hZPos).2
  calc
    Real.exp (-16 * beta) * (∫ h, W h ∂μ) <=
        Real.exp (-16 * beta) * (Real.exp (16 * beta) * W g) :=
      mul_le_mul_of_nonneg_left hZUpper (Real.exp_pos _).le
    _ = W g := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp

/-- Every nonnegative continuous gauge test under the literal posterior
one-link conditional law dominates the corresponding Haar expectation by the
same uniform exp(-16 beta) factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_ge_exp_neg_sixteen_mul_haar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : Continuous phi)
    (hphiNonneg : ∀ g, 0 <= phi g) :
    Real.exp (-16 * beta) *
        (∫ g, phi g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) <=
      ∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let p :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H N hN beta hbeta B A target
  have hpContinuous : Continuous p := by
    simpa [p] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
        H N hN beta hbeta B A target
  have hLeftInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Real.exp (-16 * beta) * phi g)
        μ :=
    (continuous_const.mul hphi).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRightInt :
      Integrable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          phi g * p g)
        μ :=
    (hphi.mul hpContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
      H N hN beta hbeta B A target phi hphi]
  change
    Real.exp (-16 * beta) * (∫ g, phi g ∂μ) <=
      ∫ g, phi g * p g ∂μ
  rw [← integral_const_mul]
  apply integral_mono hLeftInt hRightInt
  intro g
  exact mul_le_mul_of_nonneg_left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_exp_neg_sixteen_mul_le
      H N hN beta hbeta B A target g)
    (hphiNonneg g)

end

end MathlibAnalytic
end MGAP4D
