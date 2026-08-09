import MGAP4D.MathlibAnalytic.PhysicalYangMillsFloorExponentialTransferTrajectory
import Mathlib.Tactic

noncomputable section

open Filter Set Topology

namespace MGAP4D
namespace MathlibAnalytic

/-- Generic positive mass-gap lower-bound input at the Dirichlet-defect level.

Unlike `PositiveDirichletDefectScaling`, this structure does **not** assume an
exact first-order limit.  It only requires the eventual one-sided estimate

`2 * m * a_n <= delta_n`

for some `m > 0`, where `delta_n` is a squared transfer-norm defect.  This is the
natural quantitative input for proving a mass-gap lower bound rather than an
exact mass value. -/
structure PositiveDirichletDefectLowerBound
    (latticeSpacing defect : ℕ → ℝ) where
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  defect_nonneg : ∀ n, 0 ≤ defect n
  defect_lt_one : ∀ n, defect n < 1
  mass : ℝ
  mass_pos : 0 < mass
  eventually_defect_lower :
    ∀ᶠ n in atTop, 2 * mass * latticeSpacing n ≤ defect n

namespace PositiveDirichletDefectLowerBound

variable {latticeSpacing defect : ℕ → ℝ}

/-- The transfer factor canonically determined by the squared norm defect. -/
def transferFactor
    (_A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (n : ℕ) : ℝ :=
  Real.sqrt (1 - defect n)

/-- Every defect-derived transfer factor is strictly positive. -/
theorem transferFactor_pos
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (n : ℕ) :
    0 < A.transferFactor n := by
  rw [transferFactor, Real.sqrt_pos]
  exact sub_pos.mpr (A.defect_lt_one n)

/-- Every defect-derived transfer factor is nonnegative. -/
theorem transferFactor_nonneg
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (n : ℕ) :
    0 ≤ A.transferFactor n :=
  (A.transferFactor_pos n).le

/-- Every defect-derived transfer factor is at most one. -/
theorem transferFactor_le_one
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (n : ℕ) :
    A.transferFactor n ≤ 1 := by
  rw [transferFactor, Real.sqrt_le_one]
  linarith [A.defect_nonneg n]

/-- A pointwise linear lower bound on the Dirichlet defect yields the desired
one-step exponential contraction directly:

`2 m a_n <= delta_n  ==>  sqrt(1-delta_n) <= exp(-m a_n)`.

Only `log x <= x - 1` is used; no Taylor expansion or exact defect limit is
needed. -/
theorem transferFactor_le_exp_neg_mass_mul
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (n : ℕ)
    (hLower : 2 * A.mass * latticeSpacing n ≤ defect n) :
    A.transferFactor n ≤ Real.exp (-A.mass * latticeSpacing n) := by
  let x := 1 - defect n
  have hx : 0 < x := by
    dsimp [x]
    exact sub_pos.mpr (A.defect_lt_one n)
  have hlog := Real.log_le_sub_one_of_pos hx
  have hlogFactor :
      Real.log (A.transferFactor n) ≤ -A.mass * latticeSpacing n := by
    unfold transferFactor
    rw [Real.log_sqrt (le_of_lt hx)]
    dsimp [x] at hlog
    linarith
  calc
    A.transferFactor n =
        Real.exp (Real.log (A.transferFactor n)) :=
      (Real.exp_log (A.transferFactor_pos n)).symm
    _ ≤ Real.exp (-A.mass * latticeSpacing n) :=
      Real.exp_le_exp.mpr hlogFactor

/-- The one-step exponential contraction holds eventually along the lattice
sequence. -/
theorem eventually_transferFactor_le_exp_neg_mass_mul
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect) :
    ∀ᶠ n in atTop,
      A.transferFactor n ≤ Real.exp (-A.mass * latticeSpacing n) := by
  filter_upwards [A.eventually_defect_lower] with n hn
  exact A.transferFactor_le_exp_neg_mass_mul n hn

/-- Exact scalar identity converting a power of a one-step exponential into the
exponential at the corresponding integer lattice time. -/
theorem exp_neg_mass_spacing_pow
    (mass spacing : ℝ) (k : ℕ) :
    (Real.exp (-mass * spacing)) ^ k =
      Real.exp (-mass * ((k : ℝ) * spacing)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The eventual one-step defect lower bound therefore controls the canonical
floor-selected transfer power by the exact physical-time exponential. -/
theorem eventually_floorTransferFactorPow_le_exponential
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (t : NNReal) :
    ∀ᶠ n in atTop,
      (A.transferFactor n) ^
          physicalTemporalFloorNatStep latticeSpacing t n ≤
        Real.exp
          (-A.mass *
            ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n)) := by
  filter_upwards [A.eventually_transferFactor_le_exp_neg_mass_mul] with n hn
  let k := physicalTemporalFloorNatStep latticeSpacing t n
  calc
    (A.transferFactor n) ^ k ≤
        (Real.exp (-A.mass * latticeSpacing n)) ^ k :=
      pow_le_pow_left₀ (A.transferFactor_nonneg n) hn k
    _ = Real.exp (-A.mass * ((k : ℝ) * latticeSpacing n)) :=
      exp_neg_mass_spacing_pow A.mass (latticeSpacing n) k

/-- The bounding floor-time exponential converges to the target physical-time
exponential. -/
theorem floorExponential_tendsto
    (A : PositiveDirichletDefectLowerBound latticeSpacing defect)
    (t : NNReal) :
    Tendsto
      (fun n =>
        Real.exp
          (-A.mass *
            ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n)))
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) :=
  physicalTemporalFloorExponentialFactor_tendsto
    latticeSpacing A.latticeSpacing_pos A.latticeSpacing_tendsto_zero A.mass t

end PositiveDirichletDefectLowerBound

end MathlibAnalytic
end MGAP4D

end