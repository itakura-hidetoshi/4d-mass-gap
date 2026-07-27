import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Backward time-zero conditioning of a finite cylinder observable for a
real-linear transition operator.  For observables `[f₀, ..., fₙ]`, the recursion
encodes

`f₀ * P (f₁ * P (... P fₙ))`.

This is the algebraic finite-cylinder Markov construction; no measure-theoretic
path space is required at this layer. -/
def linearMarkovCylinderCondition
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) :
    List (Ω → ℝ) → (Ω → ℝ)
  | [] => fun _ => 1
  | f :: fs => fun x => f x * P (linearMarkovCylinderCondition P fs) x

@[simp] theorem linearMarkovCylinderCondition_nil
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) :
    linearMarkovCylinderCondition P [] = fun _ => 1 :=
  rfl

@[simp] theorem linearMarkovCylinderCondition_cons
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (f : Ω → ℝ)
    (fs : List (Ω → ℝ))
    (x : Ω) :
    linearMarkovCylinderCondition P (f :: fs) x =
      f x * P (linearMarkovCylinderCondition P fs) x :=
  rfl

/-- The one-coordinate cylinder has the expected time-zero conditional value
when the transition preserves constants. -/
theorem linearMarkovCylinderCondition_singleton
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (f : Ω → ℝ) :
    linearMarkovCylinderCondition P [f] = f := by
  funext x
  simp [linearMarkovCylinderCondition, hPone]

/-- The two-coordinate cylinder is the usual one-step Markov conditional
expectation `f₀ * P f₁`. -/
theorem linearMarkovCylinderCondition_pair
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (f g : Ω → ℝ) :
    linearMarkovCylinderCondition P [f, g] =
      fun x => f x * P g x := by
  funext x
  simp [linearMarkovCylinderCondition, hPone]

/-- The three-coordinate cylinder is the two-step backward Markov recursion. -/
theorem linearMarkovCylinderCondition_triple
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (f g h : Ω → ℝ) :
    linearMarkovCylinderCondition P [f, g, h] =
      fun x => f x * P (fun y => g y * P h y) x := by
  funext x
  simp [linearMarkovCylinderCondition, hPone]

/-- If the transition preserves constants, every all-one finite cylinder has
conditional value one. -/
theorem linearMarkovCylinderCondition_replicate_one
    {Ω : Type*}
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ => 1) = fun _ => 1)
    (n : ℕ) :
    linearMarkovCylinderCondition P
        (List.replicate n (fun _ : Ω => 1)) =
      fun _ => 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      funext x
      simp [List.replicate_succ, linearMarkovCylinderCondition, ih, hPone]

end

end MathlibAnalytic
end MGAP4D
