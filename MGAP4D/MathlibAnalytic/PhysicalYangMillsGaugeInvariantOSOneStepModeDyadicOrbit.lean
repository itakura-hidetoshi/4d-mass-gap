import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialSemigroupModeGenerator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalOrbitContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The unit dyadic time sequence `1, 1/2, 1/4, ...` on nonnegative Euclidean
time.  It is defined recursively so the halving identity is definitional. -/
def dyadicUnitTime : ℕ → NNReal
  | 0 => 1
  | n + 1 => dyadicUnitTime n / 2

@[simp] theorem dyadicUnitTime_zero : dyadicUnitTime 0 = 1 := rfl

@[simp] theorem dyadicUnitTime_succ (n : ℕ) :
    dyadicUnitTime (n + 1) = dyadicUnitTime n / 2 := rfl

/-- Inner-product symmetry plus the semigroup law make every positive-time
operator positive in quadratic-form sense.  Indeed `T_t = T_{t/2}^2`, and the
symmetry of `T_{t/2}` converts the quadratic form into a norm square. -/
theorem physicalOperator_inner_self_nonneg_of_innerSymmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    0 ≤ inner ℝ (T.toPhysicalSemigroup.operator t psi) psi := by
  have ht : t / 2 + t / 2 = t := by
    calc
      t / 2 + t / 2 = (t / 2) * 2 := by ring
      _ = t := by simp
  have hsplit :
      T.toPhysicalSemigroup.operator t psi =
        T.toPhysicalSemigroup.operator (t / 2)
          (T.toPhysicalSemigroup.operator (t / 2) psi) := by
    calc
      T.toPhysicalSemigroup.operator t psi =
          T.toPhysicalSemigroup.operator (t / 2 + t / 2) psi := by rw [ht]
      _ = T.toPhysicalSemigroup.operator (t / 2)
          (T.toPhysicalSemigroup.operator (t / 2) psi) := by
        rw [T.toPhysicalSemigroup.operator_add]
        rfl
  rw [hsplit, hSymmetric (t / 2)
    (T.toPhysicalSemigroup.operator (t / 2) psi) psi]
  exact real_inner_self_nonneg

/-- Positive square-root uniqueness on a semigroup mode.

If the double-time operator acts on `psi` by the strictly positive scalar
`lambda^2`, then the half-time operator must act by `lambda`.  The proof avoids
functional calculus: for `y = T_t psi - lambda psi`, semigroup composition gives
`T_t y + lambda y = 0`; positivity of `T_t` forces `y = 0`. -/
theorem physicalOperator_apply_eq_of_double_time_square_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) (lambda : ℝ)
    (hlambda : 0 < lambda)
    (hEigen :
      T.toPhysicalSemigroup.operator (t + t) psi =
        (lambda ^ 2) • psi) :
    T.toPhysicalSemigroup.operator t psi = lambda • psi := by
  let y : P.PhysicalHilbert :=
    T.toPhysicalSemigroup.operator t psi - lambda • psi
  have hdouble :
      T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator t psi) =
        (lambda ^ 2) • psi := by
    calc
      T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator t psi) =
          T.toPhysicalSemigroup.operator (t + t) psi := by
        rw [T.toPhysicalSemigroup.operator_add]
        rfl
      _ = (lambda ^ 2) • psi := hEigen
  have hyEquation :
      T.toPhysicalSemigroup.operator t y + lambda • y = 0 := by
    dsimp [y]
    rw [map_sub, map_smul, hdouble]
    module
  have hpos :
      0 ≤ inner ℝ (T.toPhysicalSemigroup.operator t y) y :=
    T.physicalOperator_inner_self_nonneg_of_innerSymmetric hSymmetric t y
  have hinner := congrArg (fun z : P.PhysicalHilbert => inner ℝ z y) hyEquation
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hinner
  have hnormSq : ‖y‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖y‖]
  have hy : y = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hnormSq
  exact sub_eq_zero.mp hy

/-- Halving an exact exponential mode preserves the exponential law.  This is
the analytic square-root step that will be iterated along dyadic times. -/
theorem physicalOperator_half_apply_of_exponential_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (c : ℝ) (t : NNReal) (psi : P.PhysicalHilbert)
    (hEigen :
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (c * (t : ℝ)) • psi) :
    T.toPhysicalSemigroup.operator (t / 2) psi =
      Real.exp (c * ((t / 2 : NNReal) : ℝ)) • psi := by
  let lambda : ℝ := Real.exp (c * ((t / 2 : NNReal) : ℝ))
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have htime : t / 2 + t / 2 = t := by
    calc
      t / 2 + t / 2 = (t / 2) * 2 := by ring
      _ = t := by simp
  have hlambdaSq : lambda ^ 2 = Real.exp (c * (t : ℝ)) := by
    dsimp [lambda]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  apply T.physicalOperator_apply_eq_of_double_time_square_eigen
    hSymmetric (t / 2) psi lambda hlambda
  rw [htime, hlambdaSq]
  exact hEigen

/-- A one-step positive eigenmode determines its exact exponential action at all
unit dyadic times `2^{-n}`.  No Hamiltonian or logarithmic-generator domain is
used here; this is purely a theorem about the bounded symmetric contraction
semigroup. -/
theorem physicalOperator_dyadicUnitTime_apply_of_one_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) (mu : ℝ) (hmu : 0 < mu)
    (hOne : T.toPhysicalSemigroup.operator 1 psi = mu • psi) :
    ∀ n : ℕ,
      T.toPhysicalSemigroup.operator (dyadicUnitTime n) psi =
        Real.exp (Real.log mu * ((dyadicUnitTime n : NNReal) : ℝ)) • psi := by
  intro n
  induction n with
  | zero =>
      simpa [dyadicUnitTime, Real.exp_log hmu]
        using hOne
  | succ n ih =>
      simpa [dyadicUnitTime] using
        T.physicalOperator_half_apply_of_exponential_eigen
          hSymmetric (Real.log mu) (dyadicUnitTime n) psi ih

/-- Once a vector is an exponential eigenmode at one time `t`, semigroup
composition propagates the same law to every natural multiple of `t`. -/
theorem physicalOperator_nsmul_time_apply_of_exponential_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (c : ℝ) (t : NNReal) (psi : P.PhysicalHilbert)
    (hEigen :
      T.toPhysicalSemigroup.operator t psi =
        Real.exp (c * (t : ℝ)) • psi) :
    ∀ m : ℕ,
      T.toPhysicalSemigroup.operator (m • t) psi =
        Real.exp (c * (((m • t : NNReal) : ℝ))) • psi := by
  intro m
  induction m with
  | zero =>
      rw [zero_nsmul, T.toPhysicalSemigroup.operator_zero]
      simp
  | succ m ih =>
      rw [succ_nsmul, T.toPhysicalSemigroup.operator_add]
      change T.toPhysicalSemigroup.operator (m • t)
          (T.toPhysicalSemigroup.operator t psi) = _
      rw [hEigen, map_smul, ih, smul_smul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

/-- A one-step positive eigenmode therefore has the exact logarithmic
exponential orbit on every nonnegative dyadic time `m / 2^n`. -/
theorem physicalOperator_dyadicTime_apply_of_one_eigen
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) (mu : ℝ) (hmu : 0 < mu)
    (hOne : T.toPhysicalSemigroup.operator 1 psi = mu • psi)
    (m n : ℕ) :
    T.toPhysicalSemigroup.operator (m • dyadicUnitTime n) psi =
      Real.exp
        (Real.log mu * (((m • dyadicUnitTime n : NNReal) : ℝ))) • psi := by
  apply T.physicalOperator_nsmul_time_apply_of_exponential_eigen
  exact T.physicalOperator_dyadicUnitTime_apply_of_one_eigen
    hSymmetric psi mu hmu hOne n

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
