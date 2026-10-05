import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteResponseBootstrap
import Mathlib.Tactic

/-!
# Common posterior one-link fixed points are constant

The finite response bootstrap of PR #5169 leaves only the terminal covariance
of a high random-scan iterate.  To identify the possible terminal limits
without assuming strict Dobrushin contraction, this file proves a purely
algebraic rigidity statement.

For a bounded continuous observable O on the finite spatial-slice
configuration space, suppose O is fixed by every exact posterior one-link
conditional expectation P_e:

  P_e O = O  for every spatial link e.

Each P_e O is independent of the current value of coordinate e.  Therefore O
itself is invariant under changing coordinate e.  Since the spatial-link index
set is finite, changing coordinates one at a time connects any two
configurations, so O is constant.

Consequently every common one-link fixed bounded-continuous observable has
zero posterior covariance with every bounded-continuous observable.

This theorem uses no strict Dobrushin row-sum estimate and no convergence
claim.  It identifies the unique possible bounded-continuous common fixed
space needed by the next terminal-remainder convergence step.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorCommonFixedSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Abstract finite-product lemma: invariance under replacing one coordinate
at a time forces a function to be globally constant. -/
theorem function_eq_of_update_invariant
    {E G R : Type*}
    [Fintype E]
    [DecidableEq E]
    (f : (E → G) → R)
    (hUpdate : ∀ (A : E → G) (e : E) (g : G),
      f (Function.update A e g) = f A)
    (A C : E → G) :
    f A = f C := by
  let replaceOn (s : Finset E) : E → G :=
    fun e => if e ∈ s then C e else A e
  have hReplace :
      ∀ s : Finset E, f (replaceOn s) = f A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [replaceOn]
    | @insert e s he ih =>
        have hConfig :
            replaceOn (insert e s) =
              Function.update (replaceOn s) e (C e) := by
          funext x
          by_cases hx : x = e
          · subst x
            simp [replaceOn]
          · simp [replaceOn, hx]
        rw [hConfig, hUpdate (replaceOn s) e (C e), ih]
  have hAll := hReplace Finset.univ
  have hUniv : replaceOn Finset.univ = C := by
    funext e
    simp [replaceOn]
  rw [hUniv] at hAll
  exact hAll.symm

/-- If an observable is fixed by the exact posterior conditional expectation
at a target link, then it is invariant under replacing that target coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_commonFixed_update_invariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hFixed :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O =
          O)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    O (Function.update A target g) = O A := by
  have hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        (Function.update A target g) A target := by
    intro e he
    simp [Function.update, he]
  have hConditional :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_of_agreeOffTarget
      H N hN beta hbeta B
      (Function.update A target g) A target O hAgree
  calc
    O (Function.update A target g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O
          (Function.update A target g) := by
      rw [hFixed target]
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O (Function.update A target g) target := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply]
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target :=
      hConditional
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O A := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply]
    _ = O A := by
      rw [hFixed target]

/-- Every bounded-continuous observable fixed by all exact posterior one-link
conditional expectations is constant on the whole finite configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_commonFixed_eq_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hFixed :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O =
          O) :
    O =
      BoundedContinuousFunction.const
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (O (fun _ => 1)) := by
  ext A
  have hConst :
      O A = O (fun _ => 1) := by
    apply function_eq_of_update_invariant
      (fun C :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        O C)
    · intro C e g
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_commonFixed_update_invariant
          H N hN beta hbeta B O hFixed C e g
    · exact A
    · exact fun _ => 1
  simpa using hConst

/-- Posterior mean of a constant bounded-continuous observable is that
constant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (c : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (BoundedContinuousFunction.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          c) =
      c := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ _A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      c ∂mu) = c
  simp

/-- A constant right observable has zero posterior covariance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_const_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (c : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F
        (BoundedContinuousFunction.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          c) =
      0 := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hFInt : Integrable (fun A => F A) mu :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_const
      H N hN beta hbeta B c]
  change
    (∫ A, F A * c ∂mu) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B F * c =
      0
  rw [integral_mul_const]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  rfl

/-- Hence every common posterior one-link fixed observable has zero covariance
with every bounded-continuous observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_commonFixed_right_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hFixed :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O =
          O) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B F O =
      0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_commonFixed_eq_const
      H N hN beta hbeta B O hFixed]
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_const_right
      H N hN beta hbeta B F (O (fun _ => 1))

end

end MathlibAnalytic
end MGAP4D
