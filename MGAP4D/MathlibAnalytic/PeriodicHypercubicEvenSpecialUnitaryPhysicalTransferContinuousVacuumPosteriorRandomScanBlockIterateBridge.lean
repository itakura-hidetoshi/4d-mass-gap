import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanDoeblinGeometricContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanVariationIteration
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Exact bridge between posterior random-scan kernels and BCF iterates

The Doeblin route of PRs #5172--#5174 is expressed with genuine Markov kernels,
whereas the covariance telescope of PRs #5164--#5169 is expressed with the
bounded-continuous posterior random-scan operator.  This file proves that these
are literally the same finite dynamics.

In particular, if L is the canonical all-spatial-link schedule length, then

  P_block^k f = P_scan^(k * L) f

pointwise, with the right-hand side exactly the observable component carried by
the existing centered random-scan state.  The centered profile is proof data
only; the observable itself is never recentered.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance posteriorRandomScanBlockIterateBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorRandomScanBlockIterateBridgeTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanBlockIterateBridgeCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanBlockIterateBridgeSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanBlockIterateBridgeMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanBlockIterateBridgeBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Integration against one full-configuration posterior heat-bath row is
exactly the pre-existing one-link posterior BCF conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_integral_eq_conditionalExpectationBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫ X, O X ∂
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
        H N hN beta hbeta B target A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_apply_eq_map_conditionalMeasure]
  have hUpdate :
      AEMeasurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta B A target) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target).comp (measurable_const.prodMk measurable_id) |>.aemeasurable
  rw [
    MeasureTheory.integral_map
      hUpdate
      O.continuous.aestronglyMeasurable]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta B O A target).symm

/-- The existing observable-level posterior random-scan expectation is exactly
integration against the exact uniform posterior random-scan kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF_eq_integral_randomScanKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
        H N hN beta hbeta B O A =
      ∫ X, O X ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
          H N hN beta hbeta B A := by
  classical
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_apply]
  rw [integral_smul_measure]
  rw [integral_finset_sum_measure (fun target _ => by
    let mu :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel
        H N hN beta hbeta B target A
    letI : IsProbabilityMeasure mu := by
      dsimp [mu]
      infer_instance
    exact
      O.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHeatBathKernel_integral_eq_conditionalExpectationBCF]
  simp [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Kernel integration is exactly the bounded-continuous posterior random-scan
Feller step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_integral_eq_randomScanConditionalExpectationContinuousBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫ X, O X ∂
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
        H N hN beta hbeta B A) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
        H N hN beta hbeta B O A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF_apply]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationBCF_eq_integral_randomScanKernel
      H N hN beta hbeta B O A).symm

/-- Integrating the initial observable of a centered random-scan state against
the exact n-step posterior random-scan kernel gives exactly the observable
component of the existing n-step centered state. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_integral_eq_centeredStateIterate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    ∀ (n : ℕ)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      (∫ X, S.observable X ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B n A) =
        (S.randomScanIterate D n).observable A := by
  intro n
  induction n with
  | zero =>
      intro A
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_zero,
        Kernel.id_apply]
      exact
        integral_dirac' S.observable A
          S.observable.continuous.stronglyMeasurable
  | succ n ih =>
      intro A
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B n
      let Q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel
          H N hN beta hbeta B
      let On :=
        (S.randomScanIterate D n).observable
      have hCompInt : Integrable S.observable ((K ∘ₖ Q) A) := by
        letI : IsProbabilityMeasure ((K ∘ₖ Q) A) := by infer_instance
        exact
          S.observable.continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      have hFubini :=
        ProbabilityTheory.Kernel.integral_comp
          (η := K) (κ := Q) (a := A) hCompInt
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_succ]
      change (∫ X, S.observable X ∂(K ∘ₖ Q) A) = _
      calc
        (∫ X, S.observable X ∂(K ∘ₖ Q) A) =
            ∫ C, (∫ X, S.observable X ∂K C) ∂Q A := by
              simpa using hFubini
        _ = ∫ C, On C ∂Q A := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun C => by
            dsimp [On]
            exact ih C
        _ =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanConditionalExpectationContinuousBCF
              H N hN beta hbeta B On A := by
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanKernel_integral_eq_randomScanConditionalExpectationContinuousBCF
              H N hN beta hbeta B On A
        _ = (S.randomScanIterate D (n + 1)).observable A := by
          rfl

/-- Finite centered-state random-scan iteration is additive in the update
count. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_add
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (m n : ℕ) :
    (S.randomScanIterate D m).randomScanIterate D n =
      S.randomScanIterate D (m + n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ,
        ih,
        Nat.add_succ,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_succ]

/-- Iterating complete posterior blocks is exactly the existing one-step BCF
random-scan iterate at the corresponding multiple of the all-link schedule
length. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_eq_centeredStateIterate_mul_scheduleLength
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (S :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
        H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    ∀ (k : ℕ)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B S.observable k A =
        (S.randomScanIterate D
          (k *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length)).observable A := by
  intro k
  induction k with
  | zero =>
      intro A
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
      ]
  | succ k ih =>
      intro A
      let L :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length
      let m := k * L
      let Sk := S.randomScanIterate D m
      have hFnEq :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
              H N hN beta hbeta B S.observable k =
            Sk.observable := by
        funext C
        dsimp [Sk, m, L]
        exact ih C
      change
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectation
            H N hN beta hbeta B
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate
              H N hN beta hbeta B S.observable k) A =
          (S.randomScanIterate D ((k + 1) * L)).observable A
      rw [hFnEq]
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectation
      calc
        (∫ X, Sk.observable X ∂
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
            H N hN beta hbeta B L A) =
          (Sk.randomScanIterate D L).observable A := by
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel_integral_eq_centeredStateIterate
                Sk D L A
        _ = (S.randomScanIterate D (m + L)).observable A := by
          rw [
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_add]
        _ = (S.randomScanIterate D ((k + 1) * L)).observable A := by
          simp [m, Nat.succ_mul]

end

end MathlibAnalytic
end MGAP4D
