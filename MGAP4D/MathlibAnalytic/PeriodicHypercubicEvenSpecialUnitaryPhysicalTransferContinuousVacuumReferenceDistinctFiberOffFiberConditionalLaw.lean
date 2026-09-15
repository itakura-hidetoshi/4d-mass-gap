import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberTransport
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceDistinctFiberOffFiberConditionalLawSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberOffFiberConditionalLawSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberOffFiberConditionalLawSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberOffFiberConditionalLawSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberOffFiberConditionalLawSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberOffFiberConditionalLawSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Distinct coordinate updates commute in the exact spatial-slice replacement
carrier.  This is the bookkeeping bridge that lets the raw reference-weight
Harnack theorem act on the off-fiber background while the integration variable
is inserted on the resampled fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_update_distinct
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : backgroundFiber ≠ fiber)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N (Function.update A backgroundFiber g) fiber u =
      Function.update
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A fiber u)
        backgroundFiber g := by
  classical
  funext e
  by_cases heFiber : e = fiber
  · subst e
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      hDistinct]
  · by_cases heBackground : e = backgroundFiber
    · subst e
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
        heFiber]
    · simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
        heFiber, heBackground]

/-- The raw `exp (32 * beta)` off-fiber Harnack comparison survives
normalization with exactly one additional Harnack factor.  Thus the two literal
C5 one-link fiber probability laws obtained by changing a distinct background
coordinate mutually dominate one another by `exp (32 * beta)^2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pairwise_harnack_update_distinct_background
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : backgroundFiber ≠ fiber)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber g) ≤
        (R * R) •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k g₂
            (Function.update A backgroundFiber h) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber h) ≤
        (R * R) •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k g₂
            (Function.update A backgroundFiber g) := by
  dsimp only
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber g)
  let w₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber h)
  let q₁ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (w₁ u)
  let q₂ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (w₂ u)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := ENNReal.ofReal_ne_top
  have hWeight : ∀ u, w₁ u ≤ Real.exp (32 * beta) * w₂ u ∧
      w₂ u ≤ Real.exp (32 * beta) * w₁ u := by
    intro u
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B target source backgroundFiber k g₂
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A fiber u)
        g h
    have hCfgG :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_update_distinct
        H N A fiber backgroundFiber hDistinct u g
    have hCfgH :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_update_distinct
        H N A fiber backgroundFiber hDistinct u h
    dsimp [w₁, w₂,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight]
    rw [hCfgG, hCfgH]
    exact hRaw
  have hq12 : ∀ u, q₁ u ≤ R * q₂ u := by
    intro u
    have hReal := (hWeight u).1
    change ENNReal.ofReal (w₁ u) ≤
      ENNReal.ofReal (Real.exp (32 * beta)) * ENNReal.ofReal (w₂ u)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hReal
  have hq21 : ∀ u, q₂ u ≤ R * q₁ u := by
    intro u
    have hReal := (hWeight u).2
    change ENNReal.ofReal (w₂ u) ≤
      ENNReal.ofReal (Real.exp (32 * beta)) * ENNReal.ofReal (w₁ u)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hReal
  have hCmp :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      μ q₁ q₂ R hR0 hRtop hq12 hq21
  simpa [
    μ, w₁, w₂, q₁, q₂, R,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure,
    realIntegralWeightedProbabilityMeasure] using hCmp

/-- After normalizing the literal C5 fiber density, changing one distinct
left-background fiber changes every bounded measurable test by at most the
mutual-Harnack coefficient induced by the raw `exp (32 * beta)` weight
comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_update_distinct_background
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : backgroundFiber ≠ fiber)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ u, |phi u| ≤ 1) :
    |(∫ u, phi u
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber g)) -
      (∫ u, phi u
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂
          (Function.update A backgroundFiber h))| ≤
      2 *
        (((Real.exp (32 * beta)) ^ 2 - 1) /
          ((Real.exp (32 * beta)) ^ 2 + 1)) := by
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber g)
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target source fiber k g₂
      (Function.update A backgroundFiber h)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
  let K : ℝ := (Real.exp (32 * beta)) ^ 2
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber g)
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber h)
  have hCmp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pairwise_harnack_update_distinct_background
      H N hN beta hbeta B target source fiber backgroundFiber hDistinct k g₂ A g h
  have hR2 : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [pow_two, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hμ12 : μ₁ ≤ ENNReal.ofReal K • μ₂ := by
    have hCmp12 := hCmp.1
    change μ₁ ≤ (R * R) • μ₂ at hCmp12
    rwa [hR2] at hCmp12
  have hμ21 : μ₂ ≤ ENNReal.ofReal K • μ₁ := by
    have hCmp21 := hCmp.2
    change μ₂ ≤ (R * R) • μ₁ at hCmp21
    rwa [hR2] at hCmp21
  have hExp : 1 ≤ Real.exp (32 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (32 * beta)]
  simpa [μ₁, μ₂, K] using
    probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μ₁ μ₂ K hK hμ12 hμ21 phi hphi hphiBound

/-- Explicit physical left-left coefficient supplied by the normalized literal
C5 conditional law.  It is deliberately independent of the structurally-zero
left-left block of the old one-way tagged carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
    (beta : ℝ) : ℝ :=
  2 * (((Real.exp (32 * beta)) ^ 2 - 1) /
    ((Real.exp (32 * beta)) ^ 2 + 1))

end

end MathlibAnalytic
end MGAP4D
