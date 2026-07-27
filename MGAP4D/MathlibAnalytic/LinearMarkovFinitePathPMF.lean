import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMFStationarity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The honest finite path probability mass function of a Markov transition.
The parameter `n` is the number of transitions, so the path has `n + 1`
coordinates. -/
def linearMarkovFinitePathPMF
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) :
    (n : ℕ) → PMF (Fin (n + 1) → Ω)
  | 0 => initial.map fun x _ => x
  | n + 1 =>
      (linearMarkovFinitePathPMF initial transition n).bind fun path =>
        (transition (path (Fin.last n))).map fun y =>
          Fin.snoc path y

/-- Deleting the terminal coordinate from an arbitrary finite Markov path PMF
recovers the preceding finite path PMF. -/
theorem linearMarkovFinitePathPMF_succ_map_init
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition (n + 1)).map Fin.init =
      linearMarkovFinitePathPMF initial transition n := by
  rw [linearMarkovFinitePathPMF, PMF.map_bind]
  have hKernel :
      (fun path =>
        ((transition (path (Fin.last n))).map fun y =>
          Fin.snoc path y).map Fin.init) =
        PMF.pure := by
    funext path
    rw [PMF.map_comp]
    simpa [Function.comp_def] using
      (PMF.map_const
        (p := transition (path (Fin.last n)))
        (b := path))
  rw [hKernel, PMF.bind_pure]

/-- The time-zero marginal of every finite Markov path PMF is the initial PMF. -/
theorem linearMarkovFinitePathPMF_map_zero
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition n).map
        (fun path => path 0) =
      initial := by
  induction n with
  | zero =>
      rw [linearMarkovFinitePathPMF, PMF.map_comp]
      simpa [Function.comp_def] using PMF.map_id initial
  | succ n ih =>
      calc
        (linearMarkovFinitePathPMF initial transition (n + 1)).map
            (fun path => path 0) =
          ((linearMarkovFinitePathPMF initial transition (n + 1)).map
              Fin.init).map
            (fun path => path 0) := by
              rw [PMF.map_comp]
              rfl
        _ =
          (linearMarkovFinitePathPMF initial transition n).map
              (fun path => path 0) := by
                rw [linearMarkovFinitePathPMF_succ_map_init]
        _ = initial := ih

/-- Under expectation stationarity, the terminal marginal of every finite
Markov path PMF is the initial PMF. -/
theorem linearMarkovFinitePathPMF_map_last_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f)
    (n : ℕ) :
    (linearMarkovFinitePathPMF initial transition n).map
        (fun path => path (Fin.last n)) =
      initial := by
  induction n with
  | zero =>
      simpa using
        linearMarkovFinitePathPMF_map_zero initial transition 0
  | succ n ih =>
      apply finite_pmf_eq_of_expectationReal_eq
      intro f
      rw [finite_pmfExpectationReal_map]
      rw [linearMarkovFinitePathPMF]
      rw [finite_pmfExpectationReal_bind]
      simp_rw [finite_pmfExpectationReal_map]
      simp only [Fin.snoc_last]
      calc
        finitePMFExpectationReal
            (linearMarkovFinitePathPMF initial transition n)
            (fun path =>
              finitePMFExpectationReal
                (transition (path (Fin.last n))) f) =
          finitePMFExpectationReal
            ((linearMarkovFinitePathPMF initial transition n).map
              (fun path => path (Fin.last n)))
            (fun x => finitePMFExpectationReal (transition x) f) := by
              rw [finite_pmfExpectationReal_map]
        _ = finitePMFExpectationReal initial
            (fun x => finitePMFExpectationReal (transition x) f) := by
              rw [ih]
        _ = finitePMFExpectationReal initial f := hstationary f

/-- Under expectation stationarity, every coordinate marginal of every finite
Markov path PMF is the initial PMF. -/
theorem linearMarkovFinitePathPMF_map_eval_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f)
    (n : ℕ)
    (i : Fin (n + 1)) :
    (linearMarkovFinitePathPMF initial transition n).map
        (fun path => path i) =
      initial := by
  induction n with
  | zero =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact linearMarkovFinitePathPMF_map_zero initial transition 0
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact
          linearMarkovFinitePathPMF_map_last_of_expectation_stationary
            initial transition hstationary (n + 1)
      · calc
          (linearMarkovFinitePathPMF initial transition (n + 1)).map
              (fun path => path j.castSucc) =
            ((linearMarkovFinitePathPMF initial transition (n + 1)).map
                Fin.init).map
              (fun path => path j) := by
                rw [PMF.map_comp]
                rfl
          _ =
            (linearMarkovFinitePathPMF initial transition n).map
                (fun path => path j) := by
                  rw [linearMarkovFinitePathPMF_succ_map_init]
          _ = initial := ih j

/-- Every point probability of every finite Markov path PMF is nonnegative. -/
theorem linearMarkovFinitePathPMF_nonneg
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (path : Fin (n + 1) → Ω) :
    0 ≤ linearMarkovFinitePathPMF initial transition n path :=
  bot_le

end

end MathlibAnalytic
end MGAP4D
