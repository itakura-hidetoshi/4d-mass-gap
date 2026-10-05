import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSingleLinkConditional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-!
# Feller closure for continuous-vacuum posterior one-link conditionals

PR #5159 identifies the literal posterior one-link conditional density with the
continuous ground-state one-link density.  This file proves the complementary
carrier facts needed for iteration:

* the target-replacement map is jointly continuous in environment and inserted
  gauge value;
* the posterior fiber log weight is jointly continuous;
* the fiber partition function and bounded-continuous numerator are continuous
  in the environment;
* the normalized posterior one-link conditional expectation is continuous and
  therefore closes in BoundedContinuousFunction;
* all of these conditional objects depend only on the off-target environment.

This is finite-volume compact-product/Feller algebra only.  No stationarity,
strict Dobrushin coefficient, geometric decay, Euclidean-time identification,
H1-D5 exact descent, or complete Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Filter

noncomputable section

local instance posteriorSingleLinkFellerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorSingleLinkFellerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorSingleLinkFellerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorSingleLinkFellerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorSingleLinkFellerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Joint continuity of replacing one posterior configuration coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update z.1 target z.2) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e = target
  · subst e
    simpa [Function.update] using
      (continuous_snd :
        Continuous
          (fun z :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                Matrix.specialUnitaryGroup (Fin N) ℂ =>
            z.2))
  · simpa [Function.update, he] using
      ((continuous_apply e).comp
        (continuous_fst :
          Continuous
            (fun z :
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                  Matrix.specialUnitaryGroup (Fin N) ℂ =>
              z.1)))

/-- The posterior target-fiber log weight is jointly continuous in the ambient
environment and inserted target value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_prod_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H N hN beta hbeta B z.1 target z.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberWeight
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_continuous
      H N hN beta hbeta B).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N target)

/-- Positive fiber Boltzmann factor associated with the posterior fiber log
weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta B A target g)

/-- The posterior fiber Boltzmann factor is jointly continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_prod_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
          H N hN beta hbeta B z.1 target z.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
  exact
    Real.continuous_exp.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_prod_continuous
        H N hN beta hbeta B target)

/-- Haar partition function of one posterior target fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
      H N hN beta hbeta B A target g
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- The posterior target-fiber partition function is continuous in the ambient
environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
          H N hN beta hbeta B A target) := by
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
        H N hN beta hbeta B z.1 target z.2
  have hF : Continuous F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_prod_continuous
        H N hN beta hbeta B target
  let FB : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hMeas :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        AEStronglyMeasurable (fun g => F (A, g))
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∀ᵐ g : Matrix.specialUnitaryGroup (Fin N) ℂ
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ),
          ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => FB.norm_coe_le_norm (A, g)
  have hContinuousParameter :
      ∀ᵐ g : Matrix.specialUnitaryGroup (Fin N) ℂ
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ),
        Continuous (fun A => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
  exact
    continuous_of_dominated
      (bound := fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => ‖FB‖)
      hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- Every posterior target-fiber partition function is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
        H N hN beta hbeta B A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
  exact
    integral_exp_pos
      ((Real.continuous_exp.comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
          H N hN beta hbeta B A target)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

/-- Unnormalized posterior one-link numerator for a bounded-continuous
configuration observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
        H N hN beta hbeta B A target g *
      O (Function.update A target g)
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- The unnormalized posterior one-link numerator is continuous in the ambient
environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
          H N hN beta hbeta B O A target) := by
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
          H N hN beta hbeta B z.1 target z.2 *
        O (Function.update z.1 target z.2)
  have hF : Continuous F := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_prod_continuous
        H N hN beta hbeta B target).mul
        (O.continuous.comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
            H N target))
  let FB : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hMeas :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        AEStronglyMeasurable (fun g => F (A, g))
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        ∀ᵐ g : Matrix.specialUnitaryGroup (Fin N) ℂ
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ),
          ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => FB.norm_coe_le_norm (A, g)
  have hContinuousParameter :
      ∀ᵐ g : Matrix.specialUnitaryGroup (Fin N) ℂ
        ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ),
        Continuous (fun A => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
  exact
    continuous_of_dominated
      (bound := fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => ‖FB‖)
      hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- Normalized posterior one-link expectation of a bounded-continuous
configuration observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
      H N hN beta hbeta B O A target /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
      H N hN beta hbeta B A target

/-- Posterior one-link conditional expectation is continuous in its ambient
environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator_continuous
      H N hN beta hbeta B O target).div
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_continuous
        H N hN beta hbeta B target)
      (fun A =>
        ne_of_gt
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_pos
            H N hN beta hbeta B A target))

/-- Feller closure of one posterior conditional expectation on the bounded
continuous carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_continuous
        H N hN beta hbeta B O target⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target O A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target :=
  rfl

private theorem posterior_update_eq_of_agreeOffTarget
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAgree : ∀ e, e ≠ target → A e = C e)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Function.update A target g = Function.update C target g := by
  funext e
  by_cases he : e = target
  · subst e
    simp
  · simp [Function.update, he, hAgree e he]

/-- Posterior fiber log weights depend only on the off-target environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_of_agreeOffTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAgree : ∀ e, e ≠ target → A e = C e) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H N hN beta hbeta B A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H N hN beta hbeta B C target := by
  funext g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberWeight
  rw [posterior_update_eq_of_agreeOffTarget A C target hAgree g]

/-- Posterior fiber partitions depend only on the off-target environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_eq_of_agreeOffTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAgree : ∀ e, e ≠ target → A e = C e) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
        H N hN beta hbeta B A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
        H N hN beta hbeta B C target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_of_agreeOffTarget
      H N hN beta hbeta B A C target hAgree]

/-- Posterior one-link conditional expectations depend only on the off-target
environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_of_agreeOffTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (hAgree : ∀ e, e ≠ target → A e = C e) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        H N hN beta hbeta B O C target := by
  have hUpdate :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        Function.update A target g = Function.update C target g :=
    posterior_update_eq_of_agreeOffTarget A C target hAgree
  have hLog :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_of_agreeOffTarget
      H N hN beta hbeta B A C target hAgree
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
  rw [hLog]
  congr 1
  apply integral_congr_ae
  filter_upwards with g
  rw [hUpdate g]

end

end MathlibAnalytic
end MGAP4D
