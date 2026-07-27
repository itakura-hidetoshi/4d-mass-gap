import MGAP4D.MathlibAnalytic.LinearMarkovCylinderCondition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Appending an unobserved terminal coordinate, represented by the constant-one
observable, does not change backward finite-cylinder conditioning. -/
theorem linearMarkovCylinderCondition_append_one
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (fs : List (Ω → ℝ)) :
    linearMarkovCylinderCondition P
        (fs ++ [fun _ : Ω => (1 : ℝ)]) =
      linearMarkovCylinderCondition P fs := by
  induction fs with
  | nil =>
      exact linearMarkovCylinderCondition_singleton P hPone
        (fun _ : Ω => (1 : ℝ))
  | cons f fs ih =>
      funext x
      simp only [List.cons_append, linearMarkovCylinderCondition_cons]
      rw [ih]

/-- A finite-cylinder moment obtained by applying an initial state functional to
backward Markov conditioning. -/
def linearMarkovCylinderMoment
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (fs : List (Ω → ℝ)) : ℝ :=
  state (linearMarkovCylinderCondition P fs)

/-- The empty cylinder is normalized whenever the initial state is normalized. -/
theorem linearMarkovCylinderMoment_nil
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hStateOne : state (fun _ => 1) = 1) :
    linearMarkovCylinderMoment state P [] = 1 := by
  simpa [linearMarkovCylinderMoment] using hStateOne

/-- One-coordinate moments recover the initial-state expectation. -/
theorem linearMarkovCylinderMoment_singleton
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (f : Ω → ℝ) :
    linearMarkovCylinderMoment state P [f] = state f := by
  rw [linearMarkovCylinderMoment,
    linearMarkovCylinderCondition_singleton P hPone]

/-- Two-coordinate moments have the expected one-step Markov form. -/
theorem linearMarkovCylinderMoment_pair
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (f g : Ω → ℝ) :
    linearMarkovCylinderMoment state P [f, g] =
      state (fun x => f x * P g x) := by
  rw [linearMarkovCylinderMoment,
    linearMarkovCylinderCondition_pair P hPone]

/-- Finite-cylinder moments are projectively consistent under deletion of an
unobserved terminal coordinate. -/
theorem linearMarkovCylinderMoment_append_one
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (fs : List (Ω → ℝ)) :
    linearMarkovCylinderMoment state P
        (fs ++ [fun _ : Ω => (1 : ℝ)]) =
      linearMarkovCylinderMoment state P fs := by
  rw [linearMarkovCylinderMoment, linearMarkovCylinderMoment,
    linearMarkovCylinderCondition_append_one P hPone fs]

end

end MathlibAnalytic
end MGAP4D
