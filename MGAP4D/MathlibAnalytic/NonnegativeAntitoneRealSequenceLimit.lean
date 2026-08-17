import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Basic

/-!
# Long-time limits of nonnegative antitone real sequences

A nonnegative antitone real sequence is bounded below by zero.  Mathlib's
monotone-convergence theorem `tendsto_atTop_ciInf` therefore identifies its
long-time limit with the conditional infimum of its values.

This generic theorem isolates the order/topological step needed by the physical
OS effective-mass sequence.
-/

namespace MGAP4D

open Filter Set
open scoped Topology

/-- A nonnegative antitone real sequence converges at `atTop` to its infimum. -/
theorem nonnegativeAntitoneRealSequence_tendsto_ciInf
    (f : ℕ → ℝ)
    (hanti : Antitone f)
    (hnonneg : ∀ n : ℕ, 0 ≤ f n) :
    Tendsto f atTop (𝓝 (⨅ n : ℕ, f n)) := by
  apply tendsto_atTop_ciInf hanti
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact hnonneg n

end MGAP4D
