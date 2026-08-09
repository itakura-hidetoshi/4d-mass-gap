import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A nonnegative target physical time has a nonnegative canonical floor step
at every positive lattice spacing.  This is the bridge from the integer-valued
floor selector used by the geometric lattice action to an honest natural
iteration count. -/
theorem physicalTemporalFloorStep_nonneg
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : NNReal) (n : ℕ) :
    0 ≤ physicalTemporalFloorStep latticeSpacing (t : ℝ) n := by
  unfold physicalTemporalFloorStep
  exact Int.floor_nonneg.2
    (div_nonneg t.coe_nonneg (latticeSpacing_pos n).le)

/-- Natural iteration count associated with the floor-selected nonnegative
physical time. -/
noncomputable def physicalTemporalFloorNatStep
    (latticeSpacing : ℕ → ℝ) (t : NNReal) (n : ℕ) : ℕ :=
  (physicalTemporalFloorStep latticeSpacing (t : ℝ) n).toNat

/-- For positive lattice spacing and nonnegative target time, converting the
canonical integer floor step to a natural number loses no information. -/
theorem physicalTemporalFloorNatStep_castInt
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : NNReal) (n : ℕ) :
    (physicalTemporalFloorNatStep latticeSpacing t n : ℤ) =
      physicalTemporalFloorStep latticeSpacing (t : ℝ) n := by
  unfold physicalTemporalFloorNatStep
  exact Int.toNat_of_nonneg
    (physicalTemporalFloorStep_nonneg latticeSpacing latticeSpacing_pos t n)

/-- Real-cast version of `physicalTemporalFloorNatStep_castInt`. -/
theorem physicalTemporalFloorNatStep_castReal
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : NNReal) (n : ℕ) :
    (physicalTemporalFloorNatStep latticeSpacing t n : ℝ) =
      ((physicalTemporalFloorStep latticeSpacing (t : ℝ) n : ℤ) : ℝ) := by
  exact_mod_cast
    physicalTemporalFloorNatStep_castInt latticeSpacing latticeSpacing_pos t n

/-- The natural floor iteration count selects physical times converging to the
prescribed nonnegative physical time. -/
theorem physicalTemporalFloorNatStep_tendsto
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (t : NNReal) :
    Tendsto
      (fun n =>
        (physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
          latticeSpacing n)
      atTop (nhds (t : ℝ)) := by
  have h := physicalTemporalFloorStep_tendsto
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero (t : ℝ)
  simpa only [physicalTemporalFloorNatStep_castReal
    latticeSpacing latticeSpacing_pos t] using h

/-- The exact exponential factor evaluated at the canonical floor-selected
physical time converges to the exact factor at the target physical time.

This is the scalar analytic kernel for passing a one-slab exponential transfer
bound to a fixed physical time before taking the right-generator limit. -/
theorem physicalTemporalFloorExponentialFactor_tendsto
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (mass : ℝ) (t : NNReal) :
    Tendsto
      (fun n =>
        Real.exp
          (-mass *
            ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n)))
      atTop (nhds (Real.exp (-mass * (t : ℝ)))) := by
  have htime := physicalTemporalFloorNatStep_tendsto
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t
  have harg :
      Tendsto
        (fun n =>
          -mass *
            ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n))
        atTop (nhds (-mass * (t : ℝ))) :=
    tendsto_const_nhds.mul htime
  exact harg.rexp

/-- A pointwise one-step norm contraction iterates with the expected geometric
factor.  No linearity, completeness, finite-dimensionality, or spectral
structure is required. -/
theorem norm_iterate_le_pow_of_norm_le
    {E : Type*} [SeminormedAddCommGroup E]
    (T : E → E) (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ x, ‖T x‖ ≤ r * ‖x‖)
    (k : ℕ) (x : E) :
    ‖T^[k] x‖ ≤ r ^ k * ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖T (T^[k] x)‖ ≤ r * ‖T^[k] x‖ := hT _
        _ ≤ r * (r ^ k * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (Nat.succ k) * ‖x‖ := by
          rw [pow_succ]
          ring

/-- Exponential one-step contractions therefore iterate with their exact
geometric power.  This theorem is deliberately kept at the normed-space level;
the identification of that power with the floor-selected physical-time
exponential is a separate scalar step. -/
theorem norm_iterate_le_exp_pow_of_norm_le
    {E : Type*} [SeminormedAddCommGroup E]
    (T : E → E) (mass spacing : ℝ)
    (hT : ∀ x, ‖T x‖ ≤ Real.exp (-mass * spacing) * ‖x‖)
    (k : ℕ) (x : E) :
    ‖T^[k] x‖ ≤ (Real.exp (-mass * spacing)) ^ k * ‖x‖ := by
  exact norm_iterate_le_pow_of_norm_le T
    (Real.exp (-mass * spacing)) (Real.exp_nonneg _) hT k x

end

end MathlibAnalytic
end MGAP4D
