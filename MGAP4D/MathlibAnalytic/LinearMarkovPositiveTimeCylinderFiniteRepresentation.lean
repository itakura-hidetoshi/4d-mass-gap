import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeCylinderAlgebra
import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeOSGram
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The strictly-positive-time prefix `(X₁, ..., Xₙ₊₁)` of a natural-time path. -/
def linearMarkovPositiveTimeFuturePrefix
    {Ω : Type*} (n : ℕ) (path : ℕ → Ω) :
    LinearMarkovPositiveTimeFuturePath Ω n :=
  fun i => path (i.1 + 1)

@[simp] theorem linearMarkovPositiveTimeFuturePrefix_apply
    {Ω : Type*} (n : ℕ) (path : ℕ → Ω) (i : Fin (n + 1)) :
    linearMarkovPositiveTimeFuturePrefix n path i = path (i.1 + 1) :=
  rfl

/-- Restrict a longer strictly-positive-time future to its first `n+1`
coordinates. -/
def linearMarkovPositiveTimeFutureRestrict
    {Ω : Type*} (n d : ℕ) :
    LinearMarkovPositiveTimeFuturePath Ω (n + d) →
      LinearMarkovPositiveTimeFuturePath Ω n :=
  fun future i => future ⟨i.1, by omega⟩

/-- Restricting a longer positive-time prefix recovers the shorter prefix. -/
@[simp] theorem linearMarkovPositiveTimeFutureRestrict_prefix
    {Ω : Type*} (n d : ℕ) (path : ℕ → Ω) :
    linearMarkovPositiveTimeFutureRestrict n d
        (linearMarkovPositiveTimeFuturePrefix (n + d) path) =
      linearMarkovPositiveTimeFuturePrefix n path := by
  rfl

/-- A natural-time observable depends on finitely many strictly-positive
coordinates when it factors through one finite positive-time prefix. -/
def LinearMarkovPositiveTimeFiniteRepresentable
    {Ω : Type*} (F : (ℕ → Ω) → ℝ) : Prop :=
  ∃ n : ℕ, ∃ H : LinearMarkovPositiveTimeFuturePath Ω n → ℝ,
    F = H ∘ linearMarkovPositiveTimeFuturePrefix n

/-- Every one-coordinate generator is represented on a finite positive-time
future. -/
theorem linearMarkovPositiveTimeCoordinate_finiteRepresentable
    {Ω : Type*} (time : ℕ) (f : Ω → ℝ) :
    LinearMarkovPositiveTimeFiniteRepresentable
      (linearMarkovPositiveTimeCoordinate time f) := by
  refine ⟨time, fun future => f (future (Fin.last time)), ?_⟩
  funext path
  rfl

/-- Constant path observables are finite positive-time observables. -/
theorem linearMarkovPositiveTime_const_finiteRepresentable
    {Ω : Type*} (r : ℝ) :
    LinearMarkovPositiveTimeFiniteRepresentable
      (fun _path : ℕ → Ω => r) := by
  refine ⟨0, fun _future => r, ?_⟩
  rfl

/-- Finite representability is closed under addition. -/
theorem LinearMarkovPositiveTimeFiniteRepresentable.add
    {Ω : Type*} {F G : (ℕ → Ω) → ℝ}
    (hF : LinearMarkovPositiveTimeFiniteRepresentable F)
    (hG : LinearMarkovPositiveTimeFiniteRepresentable G) :
    LinearMarkovPositiveTimeFiniteRepresentable (F + G) := by
  rcases hF with ⟨n, H, rfl⟩
  rcases hG with ⟨m, K, rfl⟩
  refine ⟨n + m,
    fun future =>
      H (linearMarkovPositiveTimeFutureRestrict n m future) +
        K (linearMarkovPositiveTimeFutureRestrict m n
          (by
            have h : n + m = m + n := Nat.add_comm n m
            exact h ▸ future)), ?_⟩
  funext path
  simp [Pi.add_apply, Function.comp_apply]

/-- Finite representability is closed under multiplication. -/
theorem LinearMarkovPositiveTimeFiniteRepresentable.mul
    {Ω : Type*} {F G : (ℕ → Ω) → ℝ}
    (hF : LinearMarkovPositiveTimeFiniteRepresentable F)
    (hG : LinearMarkovPositiveTimeFiniteRepresentable G) :
    LinearMarkovPositiveTimeFiniteRepresentable (F * G) := by
  rcases hF with ⟨n, H, rfl⟩
  rcases hG with ⟨m, K, rfl⟩
  refine ⟨n + m,
    fun future =>
      H (linearMarkovPositiveTimeFutureRestrict n m future) *
        K (linearMarkovPositiveTimeFutureRestrict m n
          (by
            have h : n + m = m + n := Nat.add_comm n m
            exact h ▸ future)), ?_⟩
  funext path
  simp [Pi.mul_apply, Function.comp_apply]

/-- Every element of the generated positive-time cylinder algebra factors
through one finite strictly-positive-time future. -/
theorem linearMarkovPositiveTimeCylinder_finiteRepresentable
    {Ω : Type*}
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    LinearMarkovPositiveTimeFiniteRepresentable
      (F : (ℕ → Ω) → ℝ) := by
  exact Algebra.adjoin_induction
    (p := fun G _hG => LinearMarkovPositiveTimeFiniteRepresentable G)
    (fun G hG => by
      rcases hG with ⟨time, f, rfl⟩
      exact linearMarkovPositiveTimeCoordinate_finiteRepresentable time f)
    (fun r => linearMarkovPositiveTime_const_finiteRepresentable r)
    (fun _F _G _hF _hG hF hG => hF.add hG)
    (fun _F _G _hF _hG hF hG => hF.mul hG)
    F.2

end

end MathlibAnalytic
end MGAP4D
