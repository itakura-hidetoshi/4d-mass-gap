import MGAP4D.MathlibAnalytic.FinitePMFRealExpectation
import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- On a finite state space, equality of real expectations for every real-valued
observable determines the probability mass function. -/
theorem finite_pmf_eq_of_expectationReal_eq
    {α : Type*} [Fintype α]
    (p q : PMF α)
    (h : ∀ f : α → ℝ,
      finitePMFExpectationReal p f =
        finitePMFExpectationReal q f) :
    p = q := by
  classical
  ext a
  have ha := h (fun x => if x = a then (1 : ℝ) else 0)
  simp [finitePMFExpectationReal] at ha
  calc
    p a = ENNReal.ofReal (p a).toReal := by
      symm
      exact ENNReal.ofReal_toReal_eq_iff.mpr (p.apply_ne_top a)
    _ = ENNReal.ofReal (q a).toReal := by rw [ha]
    _ = q a :=
      ENNReal.ofReal_toReal_eq_iff.mpr (q.apply_ne_top a)

/-- If one application of a finite Markov transition preserves expectation under
the initial law, then the terminal marginal of the one-step path PMF is exactly
the initial law. -/
theorem linearMarkovPairPMF_map_snd_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f) :
    (linearMarkovPairPMF initial transition).map Prod.snd =
      initial := by
  apply finite_pmf_eq_of_expectationReal_eq
  intro f
  rw [finite_pmfExpectationReal_map]
  unfold linearMarkovPairPMF
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]
  simpa using hstationary f

/-- Under the same expectation-stationarity hypothesis, the terminal marginal
of the two-step path PMF is again the initial law. -/
theorem linearMarkovTriplePMF_map_third_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f) :
    (linearMarkovTriplePMF initial transition).map
        (fun xyz => xyz.2.2) =
      initial := by
  apply finite_pmf_eq_of_expectationReal_eq
  intro f
  rw [finite_pmfExpectationReal_map]
  unfold linearMarkovTriplePMF
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_bind,
    finite_pmfExpectationReal_map]
  calc
    finitePMFExpectationReal initial
        (fun x =>
          finitePMFExpectationReal (transition x)
            (fun y => finitePMFExpectationReal (transition y) f)) =
      finitePMFExpectationReal initial
        (fun y => finitePMFExpectationReal (transition y) f) :=
        hstationary _
    _ = finitePMFExpectationReal initial f := hstationary f

end

end MathlibAnalytic
end MGAP4D
