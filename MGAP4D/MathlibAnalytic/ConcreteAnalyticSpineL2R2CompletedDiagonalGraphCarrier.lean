import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalEigenpairGraphSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Full completed diagonal graph carrier on Mathlib `l2` pairs.

A pair `(x,y)` belongs to this carrier when it satisfies the coordinate relation
`y_n = w_n x_n` for every coordinate.  This is the graph relation for the
completed diagonal action, but it is only a carrier-level definition: it does not
by itself prove closedness, self-adjointness, or any spectral theorem. -/
def concreteL2R2CompletedDiagonalGraphCarrier :
    Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)) :=
  {p | ∀ n : ℕ, p.2 n = concreteL2DiagonalWeight n * p.1 n}

/-- The obstruction-selected completed input/output pair satisfies the full
completed diagonal graph relation. -/
theorem concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph
    (k : ℕ) :
    (concreteL2R2CompletedObstructionUnitInputProbe k,
      concreteL2R2CompletedObstructionUnitOutputProbe k) ∈
        concreteL2R2CompletedDiagonalGraphCarrier := by
  intro n
  let j := concreteL2DiagonalUnboundednessObstructionSurface.witness k
  change
    (concreteL2DiagonalWeight j • concreteL2MathlibUnit j) n =
      concreteL2DiagonalWeight n * concreteL2MathlibUnit j n
  by_cases h : n = j
  · subst n
    simp [concrete_l2_mathlib_unit_apply_self]
  · have hunit : concreteL2MathlibUnit j n = 0 := by
      exact concrete_l2_mathlib_unit_apply_ne h
    simp [hunit]

/-- The completed diagonal eigenpair graph carrier is contained in the full
completed diagonal graph carrier. -/
theorem concrete_l2_r2_completed_eigenpair_graph_subset_diagonal_graph :
    concreteL2R2CompletedDiagonalEigenpairGraphCarrier ⊆
      concreteL2R2CompletedDiagonalGraphCarrier := by
  intro p hp
  rcases hp with ⟨k, rfl⟩
  exact concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph k

/-- Full completed diagonal graph growth certificate inherited from the
eigenpair graph growth certificate. -/
def concreteL2R2CompletedDiagonalGraphGrowthCertificate : Prop :=
  ∀ k : ℕ,
    ∃ p : (lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2),
      p ∈ concreteL2R2CompletedDiagonalGraphCarrier ∧
      ‖p.1‖ = 1 ∧
      (k : ℝ) < ‖p.2‖

/-- The completed diagonal graph carrier has unit-input points with arbitrarily
large certified output norm. -/
theorem concrete_l2_r2_completed_diagonal_graph_growth_certificate :
    concreteL2R2CompletedDiagonalGraphGrowthCertificate := by
  intro k
  refine ⟨
    (concreteL2R2CompletedObstructionUnitInputProbe k,
      concreteL2R2CompletedObstructionUnitOutputProbe k), ?_⟩
  exact ⟨
    concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph k,
    concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one k,
    concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k⟩

/-- Public theorem-entry predicate for the full completed diagonal graph carrier
surface. -/
def concreteAnalyticSpineL2R2CompletedDiagonalGraphCarrierReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalEigenpairGraphSurfaceReady ∧
  concreteL2R2CompletedDiagonalEigenpairGraphCarrier ⊆
    concreteL2R2CompletedDiagonalGraphCarrier ∧
  concreteL2R2CompletedDiagonalGraphGrowthCertificate

/-- The full completed diagonal graph carrier surface is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_graph_carrier_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalGraphCarrierReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_eigenpair_graph_surface_ready,
    concrete_l2_r2_completed_eigenpair_graph_subset_diagonal_graph,
    concrete_l2_r2_completed_diagonal_graph_growth_certificate⟩

end

end MathlibAnalytic
end MGAP4D
