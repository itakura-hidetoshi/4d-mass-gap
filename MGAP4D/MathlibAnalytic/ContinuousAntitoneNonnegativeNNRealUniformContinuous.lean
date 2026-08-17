import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform continuity of nonnegative antitone functions on `NNReal`

A continuous nonnegative antitone real-valued function on the nonnegative real
half-line has a finite limit at infinity, hence is uniformly continuous.  The
proof is entirely topological/order-theoretic: monotone convergence supplies
the finite tail limit, `cocompact_eq_atTop` identifies escape from compact sets
with `atTop` on `NNReal`, and Mathlib's cocompact Heine--Cantor theorem closes
the global uniform-continuity step.
-/

namespace MGAP4D

/-- A nonnegative antitone real-valued function on `NNReal` converges at
`atTop` to the infimum of its range. -/
theorem antitone_nonnegative_nnreal_tendsto_atTop_ciInf
    (f : NNReal → ℝ)
    (hantitone : Antitone f)
    (hnonneg : ∀ t, 0 ≤ f t) :
    Filter.Tendsto f Filter.atTop (nhds (⨅ t : NNReal, f t)) := by
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hnonneg t
  exact tendsto_atTop_ciInf hantitone hbdd

/-- A continuous nonnegative antitone real-valued function on `NNReal` is
uniformly continuous on the whole half-line. -/
theorem uniformContinuous_of_continuous_antitone_nonnegative_nnreal
    (f : NNReal → ℝ)
    (hcontinuous : Continuous f)
    (hantitone : Antitone f)
    (hnonneg : ∀ t, 0 ≤ f t) :
    UniformContinuous f := by
  apply hcontinuous.uniformContinuous_of_tendsto_cocompact
  rw [cocompact_eq_atTop]
  exact antitone_nonnegative_nnreal_tendsto_atTop_ciInf f hantitone hnonneg

end MGAP4D
