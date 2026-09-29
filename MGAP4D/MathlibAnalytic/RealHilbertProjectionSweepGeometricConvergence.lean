import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# A geometric-loss sweep converges to its absorbing block

The finite-list displacement estimate below is used ONLY to prove qualitative
Cauchy convergence at a fixed finite volume. Its list-length constant is not
used in any uniform energy, Schur, forcing or renewal-contraction coefficient.

Geometric path loss makes consecutive sweep displacements summable. Completeness
then gives a limit. Continuity makes it sweep-fixed; the fixed-space inclusion
and the absorbing block identify that limit with B x. No commutativity, general
cyclic-projection convergence axiom, or assumed vanishing defect tail is used.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- A coarse finite-list estimate for qualitative convergence only. No
self-adjointness, idempotence, or commutativity is needed for this estimate. -/
theorem realHilbertProjectionSweep_displacement_le_length_mul_sqrt_pathLoss
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (cs : List C) (x : E) :
    ‖x - realHilbertProjectionSweep P cs x‖ ≤
      (cs.length : ℝ) * Real.sqrt (realHilbertProjectionSweepPathLoss P cs x) := by
  induction cs generalizing x with
  | nil => simp [realHilbertProjectionSweep, realHilbertProjectionSweepPathLoss]
  | cons c cs ih =>
      let tail := realHilbertProjectionSweepPathLoss P cs (P c x)
      let total := ‖x - P c x‖ ^ 2 + tail
      have hTail0 : 0 ≤ tail := realHilbertProjectionSweepPathLoss_nonneg P cs (P c x)
      have hTotal0 : 0 ≤ total := add_nonneg (sq_nonneg _) hTail0
      have hHead : ‖x - P c x‖ ≤ Real.sqrt total := by
        have hSquare := Real.sq_sqrt hTotal0
        dsimp [total] at hSquare
        nlinarith [Real.sqrt_nonneg total, norm_nonneg (x - P c x)]
      have hTailLe : tail ≤ total := by
        dsimp [total]
        nlinarith [sq_nonneg ‖x - P c x‖]
      have hTailRoot : Real.sqrt tail ≤ Real.sqrt total := Real.sqrt_le_sqrt hTailLe
      change ‖x - realHilbertProjectionSweep P cs (P c x)‖ ≤
        ((cs.length + 1 : ℕ) : ℝ) * Real.sqrt total
      calc
        ‖x - realHilbertProjectionSweep P cs (P c x)‖ ≤
            ‖x - P c x‖ + ‖P c x - realHilbertProjectionSweep P cs (P c x)‖ := by
          simpa only [dist_eq_norm] using
            (dist_triangle x (P c x) (realHilbertProjectionSweep P cs (P c x)))
        _ ≤ Real.sqrt total + (cs.length : ℝ) * Real.sqrt total :=
          _root_.add_le_add hHead ((ih (P c x)).trans
            (mul_le_mul_of_nonneg_left hTailRoot (Nat.cast_nonneg _)))
        _ = ((cs.length + 1 : ℕ) : ℝ) * Real.sqrt total := by
          push_cast
          ring

/-- Geometric path loss along this actual orbit is sufficient. The limit is
identified with B x using absorption and the fixed-space inclusion, not by
asserting that an arbitrary Cauchy limit is in the initial bounded core. -/
theorem realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : C → E →L[ℝ] E) (cs : List C) (B : E →L[ℝ] E)
    (eta : ℝ) (hEta0 : 0 ≤ eta) (hEta1 : eta < 1)
    (hAbsorb : ∀ y : E, B (realHilbertProjectionSweep P cs y) = B y)
    (hFixedSpace : ∀ y : E, realHilbertProjectionSweep P cs y = y → B y = y)
    (x : E)
    (hDecay : ∀ n : ℕ,
      realHilbertProjectionSweepPathLoss P cs
          ((realHilbertProjectionSweep P cs : E → E)^[n] x) ≤
        eta ^ n * realHilbertProjectionSweepPathLoss P cs x) :
    Tendsto (fun n : ℕ => (realHilbertProjectionSweep P cs : E → E)^[n] x)
      atTop (𝓝 (B x)) := by
  let S : E → E := realHilbertProjectionSweep P cs
  let l0 := realHilbertProjectionSweepPathLoss P cs x
  let r := Real.sqrt eta
  have hL0 : 0 ≤ l0 := realHilbertProjectionSweepPathLoss_nonneg P cs x
  have hr0 : 0 ≤ r := Real.sqrt_nonneg eta
  have hrSquare : r ^ 2 = eta := Real.sq_sqrt hEta0
  have hr1 : r < 1 := by nlinarith
  have hStep : ∀ n : ℕ,
      dist (S^[n] x) (S^[n + 1] x) ≤
        ((cs.length : ℝ) * Real.sqrt l0) * r ^ n := by
    intro n
    have hrPow : (r ^ n) ^ 2 = eta ^ n := by
      calc
        (r ^ n) ^ 2 = (r ^ 2) ^ n := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
        _ = eta ^ n := by rw [hrSquare]
    have hRoot0 : 0 ≤ r ^ n * Real.sqrt l0 :=
      mul_nonneg (pow_nonneg hr0 n) (Real.sqrt_nonneg l0)
    have hRootSquare : (r ^ n * Real.sqrt l0) ^ 2 = eta ^ n * l0 := by
      rw [mul_pow, hrPow, Real.sq_sqrt hL0]
    have hSquareBound : realHilbertProjectionSweepPathLoss P cs (S^[n] x) ≤
        (r ^ n * Real.sqrt l0) ^ 2 := by
      rw [hRootSquare]
      exact hDecay n
    have hRootBound : Real.sqrt (realHilbertProjectionSweepPathLoss P cs (S^[n] x)) ≤
        r ^ n * Real.sqrt l0 := by
      simpa only [Real.sqrt_sq hRoot0] using Real.sqrt_le_sqrt hSquareBound
    calc
      dist (S^[n] x) (S^[n + 1] x) = ‖S^[n] x - S (S^[n] x)‖ := by
        rw [dist_eq_norm, Function.iterate_succ_apply']
      _ ≤ (cs.length : ℝ) * Real.sqrt (realHilbertProjectionSweepPathLoss P cs (S^[n] x)) :=
        realHilbertProjectionSweep_displacement_le_length_mul_sqrt_pathLoss P cs (S^[n] x)
      _ ≤ (cs.length : ℝ) * (r ^ n * Real.sqrt l0) :=
        mul_le_mul_of_nonneg_left hRootBound (Nat.cast_nonneg _)
      _ = ((cs.length : ℝ) * Real.sqrt l0) * r ^ n := by ring
  have hCauchy : CauchySeq (fun n : ℕ => S^[n] x) :=
    cauchySeq_of_le_geometric r ((cs.length : ℝ) * Real.sqrt l0) hr1 hStep
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hContinuous : Continuous S := (realHilbertProjectionSweep P cs).continuous
  have hShift : Tendsto (fun n : ℕ => S^[n + 1] x) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).2 hz
  have hFixed : S z = z :=
    tendsto_nhds_unique ((hContinuous.tendsto z).comp hz)
      (by simpa only [Function.iterate_succ_apply'] using hShift)
  have hBIter : ∀ n : ℕ, B (S^[n] x) = B x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hAbsorb _).trans ih
  have hBConst : Tendsto (fun n : ℕ => B (S^[n] x)) atTop (𝓝 (B x)) := by
    simpa only [hBIter] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => B x) atTop (𝓝 (B x)))
  have hIdentify : z = B x :=
    (hFixedSpace z hFixed).symm.trans
      (tendsto_nhds_unique ((B.continuous.tendsto z).comp hz) hBConst)
  simpa only [S, hIdentify] using hz

end
end MGAP4D.MathlibAnalytic
