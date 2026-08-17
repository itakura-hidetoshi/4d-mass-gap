import MGAP4D.MathlibAnalytic.BoundedNonnegativeSequenceOverLinearTime
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedNormalizedLogDecayOverTime

/-!
# Fixed-positive-regularization long-time effective mass is zero

For fixed `ε > 0`, the regularized correlation has the positive floor

`C̃(t) + ε ≥ ε`.

Hence its regularized logarithm is bounded below by `log ε`, while antitonicity
bounds it above by its value at time zero.  The endpoint logarithmic decay
therefore has a uniformly bounded nonnegative numerator.  Dividing by elapsed
time `n h`, with `h > 0`, forces the normalized decay rate to zero.

The preceding elapsed-time theorem identifies this same quotient with the
canonical long-time regularized effective-mass limit.  Uniqueness of limits
therefore gives

`m∞_{ε,h} = 0`.

This is an order-of-limits theorem: fixed positive regularization cannot retain a
positive long-time mass.  A positive mass route must remove the regularization
before the long-time limit, use an unregularized strictly-positive correlation,
or control a joint `ε → 0`, `t → ∞` limit.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter
open scoped Topology InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- For fixed positive regularization and positive sampling step, the normalized
endpoint regularized logarithmic decay divided by elapsed time tends to zero. -/
theorem physicalCorrelationRealClampRegularizedLogEndpoint_overElapsedTime_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        (T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
          T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) /
          ((n : ℝ) * h))
      atTop
      (𝓝 0) := by
  let f : ℕ → ℝ := fun n =>
    T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
      T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)
  let K : ℝ :=
    T.physicalCorrelationRealClampRegularizedLog psi ε 0 - Real.log ε
  have hanti :=
    T.physicalCorrelationRealClampRegularizedLog_antitone
      hSymmetric psi hε
  have hf0 : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have htime : 0 ≤ (n : ℝ) * h :=
      mul_nonneg (Nat.cast_nonneg n) hh.le
    exact sub_nonneg.mpr (hanti htime)
  have hfK : ∀ n : ℕ, f n ≤ K := by
    intro n
    have hcorr :
        0 ≤ T.physicalCorrelationRealClamp psi ((n : ℝ) * h) :=
      T.physicalCorrelationRealClamp_nonneg hSymmetric psi _
    have hsum :
        ε ≤ T.physicalCorrelationRealClamp psi ((n : ℝ) * h) + ε := by
      linarith
    have hlogLower :
        Real.log ε ≤
          T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h) := by
      unfold physicalCorrelationRealClampRegularizedLog
      exact Real.log_le_log hε hsum
    dsimp [f, K]
    linarith
  simpa [f] using
    MGAP4D.boundedNonnegativeSequence_div_natMul_tendsto_zero
      f K h hh hf0 hfK

/-- Fixed `ε > 0` forces the canonical long-time regularized effective-mass
limit to vanish. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassLimit_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h = 0 := by
  exact tendsto_nhds_unique
    (T.physicalCorrelationRealClampRegularizedLogEndpoint_overElapsedTime_tendsto_effectiveMassLimit
      hSymmetric psi hε hh)
    (T.physicalCorrelationRealClampRegularizedLogEndpoint_overElapsedTime_tendsto_zero
      hSymmetric psi hε hh)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
