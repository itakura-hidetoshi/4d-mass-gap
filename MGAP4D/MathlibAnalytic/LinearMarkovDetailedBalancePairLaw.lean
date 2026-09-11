import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMFStationarity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Reverse a one-step Markov path by swapping its two time coordinates. -/
def linearMarkovPairSwap
    {Ω : Type*} (xy : Ω × Ω) : Ω × Ω :=
  (xy.2, xy.1)

/-- One-step path reversal is involutive. -/
@[simp] theorem linearMarkovPairSwap_involutive
    {Ω : Type*} :
    Function.Involutive (@linearMarkovPairSwap Ω) := by
  rintro ⟨x, y⟩
  rfl

/-- Real pointwise detailed balance for a finite-state Markov transition. -/
def LinearMarkovDetailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) : Prop :=
  ∀ x y : Ω,
    (initial x).toReal * (transition x y).toReal =
      (initial y).toReal * (transition y x).toReal

/-- Under pointwise detailed balance, expectation under the one-step path law is
invariant under swapping the two time coordinates. -/
theorem linearMarkovPairPMF_expectation_swap_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (H : Ω × Ω → ℝ) :
    finitePMFExpectationReal
        (linearMarkovPairPMF initial transition)
        (H ∘ linearMarkovPairSwap) =
      finitePMFExpectationReal
        (linearMarkovPairPMF initial transition) H := by
  classical
  unfold linearMarkovPairPMF
  rw [finite_pmfExpectationReal_bind, finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]
  unfold finitePMFExpectationReal
  simp only [Function.comp_apply, linearMarkovPairSwap]
  calc
    ∑ x : Ω,
        (initial x).toReal *
          ∑ y : Ω, (transition x y).toReal * H (y, x) =
      ∑ x : Ω, ∑ y : Ω,
        (initial x).toReal * (transition x y).toReal * H (y, x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          ring
    _ = ∑ y : Ω, ∑ x : Ω,
        (initial x).toReal * (transition x y).toReal * H (y, x) := by
          rw [Finset.sum_comm]
    _ = ∑ y : Ω, ∑ x : Ω,
        (initial y).toReal * (transition y x).toReal * H (y, x) := by
          apply Finset.sum_congr rfl
          intro y _hy
          apply Finset.sum_congr rfl
          intro x _hx
          rw [hdb x y]
    _ = ∑ y : Ω,
        (initial y).toReal *
          ∑ x : Ω, (transition y x).toReal * H (y, x) := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring

/-- Pointwise detailed balance makes the one-step Markov path PMF exactly
invariant under time reversal. -/
theorem linearMarkovPairPMF_map_swap_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    (linearMarkovPairPMF initial transition).map linearMarkovPairSwap =
      linearMarkovPairPMF initial transition := by
  apply finite_pmf_eq_of_expectationReal_eq
  intro H
  rw [finite_pmfExpectationReal_map]
  simpa [Function.comp_def] using
    linearMarkovPairPMF_expectation_swap_of_detailedBalanceReal
      initial transition hdb H

/-- Detailed balance also yields stationarity of the terminal marginal of the
one-step path law. -/
theorem linearMarkovPairPMF_map_snd_of_detailedBalanceReal
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    (linearMarkovPairPMF initial transition).map Prod.snd = initial := by
  calc
    (linearMarkovPairPMF initial transition).map Prod.snd =
        ((linearMarkovPairPMF initial transition).map
          linearMarkovPairSwap).map Prod.fst := by
            rw [PMF.map_comp]
            rfl
    _ = (linearMarkovPairPMF initial transition).map Prod.fst := by
          rw [linearMarkovPairPMF_map_swap_of_detailedBalanceReal
            initial transition hdb]
    _ = initial :=
      linearMarkovPairPMF_map_fst initial transition

end

end MathlibAnalytic
end MGAP4D
