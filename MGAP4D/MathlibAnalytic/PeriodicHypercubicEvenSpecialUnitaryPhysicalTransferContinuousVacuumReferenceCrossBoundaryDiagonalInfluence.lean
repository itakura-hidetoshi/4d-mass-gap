import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctSourceConditionalCarrierInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetKernelHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance referenceCrossBoundaryDiagonalInfluenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceCrossBoundaryDiagonalInfluenceSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceCrossBoundaryDiagonalInfluenceSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceCrossBoundaryDiagonalInfluenceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceCrossBoundaryDiagonalInfluenceSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceCrossBoundaryDiagonalInfluenceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- When the changed right-boundary source is the same spatial link as the
resampled left fiber, the two literal C5 fiber weights are mutually controlled
by the sharp one-slab factor `exp (8 * beta)`.  All vacuum and target-local
factors are common; the only changing factor is the right-boundary one-slab
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pairwise_harnack_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
          H N hN beta hbeta B target fiber fiber k₁ g₂ A g ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
            H N hN beta hbeta B target fiber fiber k₂ g₂ A g ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
          H N hN beta hbeta B target fiber fiber k₂ g₂ A g ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
            H N hN beta hbeta B target fiber fiber k₁ g₂ A g := by
  let A' :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A fiber g
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta A'
  let Local :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A' B target g₂
  let K₁ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A' (Function.update B fiber k₁)
  let K₂ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A' (Function.update B fiber k₂)
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_pairwise_harnack
      H N hN beta hbeta A' B fiber k₁ k₂
  have hPrefix : 0 ≤ Omega * Local :=
    mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta A').le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta A' B target g₂).le
  change
    (Omega * Local) * K₁ ≤ Real.exp (8 * beta) * ((Omega * Local) * K₂) ∧
      (Omega * Local) * K₂ ≤ Real.exp (8 * beta) * ((Omega * Local) * K₁)
  constructor
  · calc
      (Omega * Local) * K₁ ≤ (Omega * Local) * (Real.exp (8 * beta) * K₂) :=
        mul_le_mul_of_nonneg_left hKernel.1 hPrefix
      _ = Real.exp (8 * beta) * ((Omega * Local) * K₂) := by ring
  · calc
      (Omega * Local) * K₂ ≤ (Omega * Local) * (Real.exp (8 * beta) * K₁) :=
        mul_le_mul_of_nonneg_left hKernel.2 hPrefix
      _ = Real.exp (8 * beta) * ((Omega * Local) * K₁) := by ring

/-- Normalization costs exactly one additional Harnack factor.  Thus changing
the right-boundary value at the same link as the resampled left fiber produces
mutual domination of the two normalized C5 fiber laws by
`exp (8 * beta)^2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pairwise_harnack_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₁ g₂ A ≤
        (R * R) •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target fiber fiber k₂ g₂ A ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₂ g₂ A ≤
        (R * R) •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target fiber fiber k₁ g₂ A := by
  dsimp only
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target fiber fiber k₁ g₂ A
  let w₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target fiber fiber k₂ g₂ A
  let q₁ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ := fun g => ENNReal.ofReal (w₁ g)
  let q₂ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ := fun g => ENNReal.ofReal (w₂ g)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := ENNReal.ofReal_ne_top
  have hq12 : ∀ g, q₁ g ≤ R * q₂ g := by
    intro g
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pairwise_harnack_diagonal
        H N hN beta hbeta B target fiber k₁ k₂ g₂ A g).1
    change ENNReal.ofReal (w₁ g) ≤
      ENNReal.ofReal (Real.exp (8 * beta)) * ENNReal.ofReal (w₂ g)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hReal
  have hq21 : ∀ g, q₂ g ≤ R * q₁ g := by
    intro g
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pairwise_harnack_diagonal
        H N hN beta hbeta B target fiber k₁ k₂ g₂ A g).2
    change ENNReal.ofReal (w₂ g) ≤
      ENNReal.ofReal (Real.exp (8 * beta)) * ENNReal.ofReal (w₁ g)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hReal
  have hCmp :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      μ q₁ q₂ R hR0 hRtop hq12 hq21
  simpa [
    μ, w₁, w₂, q₁, q₂, R,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure,
    realIntegralWeightedProbabilityMeasure] using hCmp

/-- For a bounded measurable real test, the only nontrivial cross-boundary C5
source influence is the diagonal one.  On that diagonal the exact normalized
Harnack coefficient gives the sharp mutual-domination consequence with
`K = exp (8 * beta)^2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₁ g₂ A) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₂ g₂ A)| ≤
      2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1)) := by
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target fiber fiber k₁ g₂ A
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target fiber fiber k₂ g₂ A
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  let K : ℝ := (Real.exp (8 * beta)) ^ 2
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₁ g₂ A
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₂ g₂ A
  have hCmp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pairwise_harnack_diagonal
      H N hN beta hbeta B target fiber k₁ k₂ g₂ A
  have hR2 : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [pow_two, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hμ12 : μ₁ ≤ ENNReal.ofReal K • μ₂ := by
    have h := hCmp.1
    change μ₁ ≤ (R * R) • μ₂ at h
    rwa [hR2] at h
  have hμ21 : μ₂ ≤ ENNReal.ofReal K • μ₁ := by
    have h := hCmp.2
    change μ₂ ≤ (R * R) • μ₁ at h
    rwa [hR2] at h
  have hExp : 1 ≤ Real.exp (8 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (8 * beta)]
  simpa [μ₁, μ₂, K] using
    probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μ₁ μ₂ K hK hμ12 hμ21 phi hphi hphiBound

/-- Full cross-boundary support theorem for the normalized C5 one-link fiber
law.  A right-boundary source distinct from the resampled left fiber has
exactly zero influence; only the matching source/fiber coordinate can carry a
residual, and that residual is bounded by the diagonal Harnack coefficient.
No distance-decay or full-4D Wilson conditional identification is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_supported_on_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k₁ g₂ A) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k₂ g₂ A)| ≤
      if source = fiber then
        2 *
          (((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1))
      else 0 := by
  by_cases hsf : source = fiber
  · subst source
    simpa using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_diagonal
        H N hN beta hbeta B target fiber k₁ k₂ g₂ A phi hphi hphiBound
  · have hEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_of_source_ne_fiber
        H N hN beta hbeta B target source fiber k₁ k₂ g₂ A hsf
    rw [hEq]
    simp [hsf]

end

end MathlibAnalytic
end MGAP4D
