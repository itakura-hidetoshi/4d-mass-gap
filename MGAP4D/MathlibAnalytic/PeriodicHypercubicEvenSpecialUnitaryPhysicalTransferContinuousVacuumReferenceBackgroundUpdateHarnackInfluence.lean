import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOffTargetHeatBathRawVacuumDoobBridge
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backgroundUpdateHarnackInfluenceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backgroundUpdateHarnackInfluenceSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backgroundUpdateHarnackInfluenceSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backgroundUpdateHarnackInfluenceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backgroundUpdateHarnackInfluenceSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The normalized-law influence produced by the global pairwise reference
weight Harnack factor exp (32 * beta).  Normalization costs one additional
factor, hence the probability-law domination constant is
(exp (32 * beta))^2. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
    (beta : ℝ) : ℝ :=
  let K := (Real.exp (32 * beta)) ^ 2
  2 * ((K - 1) / (K + 1))

/-- The Harnack influence is nonnegative at nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta := by
  let x : ℝ := Real.exp (32 * beta)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hK : 1 ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  change 0 ≤ 2 * (((Real.exp (32 * beta)) ^ 2 - 1) /
    ((Real.exp (32 * beta)) ^ 2 + 1))
  exact mul_nonneg (by norm_num)
    (div_nonneg (sub_nonneg.mpr (by simpa [x] using hK)) (by positivity))

/-- The Harnack influence remains strictly below the trivial full-L1 value
two for every finite coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_lt_two
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta < 2 := by
  let K : ℝ := (Real.exp (32 * beta)) ^ 2
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hden : 0 < K + 1 := by positivity
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  change 2 * ((K - 1) / (K + 1)) < 2
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- Changing one background link value at a link distinct from the resampled
fiber changes the literal normalized C5 one-link law by at most the Harnack
influence.

This is deliberately a coarse local bound: it uses the global
exp (32 * beta) pairwise reference-weight Harnack theorem and therefore
applies to active neighbors without any remote-cancellation hypothesis.  It
does not assert that this coefficient is sharp. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_boundedTest_difference_le_harnackInfluence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u)) -
      (∫ g, phi g ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta := by
  classical
  let μHaar : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber v
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Au fiber
  let vWeight : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Av fiber
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (32 * beta))
  let K : ℝ := (Real.exp (32 * beta)) ^ 2
  let μu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  let μv : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  letI : IsProbabilityMeasure μu := by
    dsimp [μu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  letI : IsProbabilityMeasure μv := by
    dsimp [μv]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  have hComm :
      ∀ (z x : Matrix.specialUnitaryGroup (Fin N) ℂ),
        Function.update (Function.update A backgroundFiber z) fiber x =
          Function.update (Function.update A fiber x) backgroundFiber z := by
    intro z x
    funext e
    by_cases hef : e = fiber
    · subst e
      simp [hDistinct]
    · by_cases heb : e = backgroundFiber
      · subst e
        simp [hef]
      · simp [hef, heb]
  have hwv : ∀ x, w x ≤ R * vWeight x := by
    intro x
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).1
    have hReal' :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Au fiber x) ≤
          Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x) := by
      rw [hComm u x, hComm v x]
      exact hReal
    dsimp [w, vWeight, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Au fiber x)) ≤
        ENNReal.ofReal
          (Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x)) :=
        ENNReal.ofReal_le_ofReal hReal'
      _ =
        ENNReal.ofReal (Real.exp (32 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Av fiber x)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hvw : ∀ x, vWeight x ≤ R * w x := by
    intro x
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).2
    have hReal' :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Av fiber x) ≤
          Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x) := by
      rw [hComm v x, hComm u x]
      exact hReal
    dsimp [w, vWeight, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
            (Function.update Av fiber x)) ≤
        ENNReal.ofReal
          (Real.exp (32 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x)) :=
        ENNReal.ofReal_le_ofReal hReal'
      _ =
        ENNReal.ofReal (Real.exp (32 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂
              (Function.update Au fiber x)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (by
      dsimp [R]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hPair :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      μHaar w vWeight R hR0 hRtop hwv hvw
  have hScalar : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    ring
  rw [hScalar] at hPair
  have hLawU : μu = doobWeightedMeasure μHaar w := by
    dsimp [μu, μHaar, w]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure]
    rfl
  have hLawV : μv = doobWeightedMeasure μHaar vWeight := by
    dsimp [μv, μHaar, vWeight]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure]
    rfl
  have hμν : μu ≤ ENNReal.ofReal K • μv := by
    rw [hLawU, hLawV]
    exact hPair.1
  have hνμ : μv ≤ ENNReal.ofReal K • μu := by
    rw [hLawU, hLawV]
    exact hPair.2
  have hExp : 1 ≤ Real.exp (32 * beta) :=
    Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg (Real.exp (32 * beta) - 1)]
  have hBound :=
    probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μu μv K hK hμν hνμ phi hphi hphiBound
  simpa [
    μu, μv, K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence] using
    hBound

end

end MathlibAnalytic
end MGAP4D
