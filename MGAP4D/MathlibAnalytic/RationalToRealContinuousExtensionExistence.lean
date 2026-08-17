import MGAP4D.MathlibAnalytic.RationalToRealContinuousStationarity

/-!
# Rational-to-real continuous extension existence for stationary families

A rational family that is already constant has an evident continuous extension to real time:
the same constant family.  The density theorem from
`RationalToRealContinuousStationarity` then shows that this extension is unique among
continuous real families.

This is an existence theorem only for the one-parameter common-shift family.  It does not
construct an `ℝ`-indexed stochastic process or extend independently varying insertion times.
-/

namespace MGAP4D

/-- A rational family equal to a fixed value at every rational point has a unique continuous
real extension. -/
theorem existsUnique_continuous_real_extension_of_rational_eq_const
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : ℚ → X) (c : X)
    (hf : ∀ q : ℚ, f q = c) :
    ∃! F : ℝ → X,
      Continuous F ∧ ∀ q : ℚ, F (q : ℝ) = f q := by
  refine ⟨fun _ : ℝ => c, ?_, ?_⟩
  · constructor
    · exact continuous_const
    · intro q
      exact (hf q).symm
  · intro F hF
    apply continuous_eq_of_eq_on_rat hF.1 continuous_const
    intro q
    exact (hF.2 q).trans (hf q)

/-- Rational stationarity itself supplies a unique continuous real extension: the constant
family with value `f 0`. -/
theorem existsUnique_continuous_real_extension_of_rational_stationary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : ℚ → X)
    (hstationary : ∀ q : ℚ, f q = f 0) :
    ∃! F : ℝ → X,
      Continuous F ∧ ∀ q : ℚ, F (q : ℝ) = f q := by
  exact
    existsUnique_continuous_real_extension_of_rational_eq_const
      f (f 0) hstationary

end MGAP4D
