import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointOperatorValue
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalIsClosedGraph

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The formal-adjoint domain candidate promoted from a carrier-level `Set` to a
Mathlib `Submodule` of the concrete real `l2` Hilbert space.

This is still before any use of Mathlib's `adjoint` or `IsSelfAdjoint` API: it is
only the clean algebraic typing of the already constructed graph-level formal
adjoint domain. -/
def concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule :
    Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) where
  carrier := concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate
  zero_mem' := concrete_l2_r2_formal_adjoint_domain_zero
  add_mem' := by
    intro x y hx hy
    exact concrete_l2_r2_formal_adjoint_domain_add hx hy
  smul_mem' := by
    intro c x hx
    exact concrete_l2_r2_formal_adjoint_domain_smul c hx

/-- The `Submodule` carrier is definitionally the formal-adjoint domain
candidate. -/
theorem concrete_l2_r2_formal_adjoint_domain_submodule_carrier_eq :
    ((concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule :
        Set (lp (fun _ : ℕ => ℝ) 2)) =
      concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) := by
  rfl

/-- The chosen formal-adjoint value is independent of the particular proof that
its input belongs to the formal-adjoint domain candidate.

This is the small proof-irrelevance bridge needed to package the chosen graph
value into a Mathlib `LinearMap`.  The proof uses the already established
single-valuedness of the formal-adjoint graph candidate, not proof irrelevance as
an axiom. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_proof_irrel
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy hy' : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy =
      concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy' := by
  exact concrete_l2_r2_formal_adjoint_graph_candidate_single_valued
    (concrete_l2_r2_formal_adjoint_operator_value_mem y hy)
    (concrete_l2_r2_formal_adjoint_operator_value_mem y hy')

/-- Additivity of the chosen formal-adjoint operator value for any supplied proof
that the sum lies in the formal-adjoint domain candidate. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_add_of_domain
    {y₁ y₂ : lp (fun _ : ℕ => ℝ) 2}
    (hy₁ : y₁ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hy₂ : y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hysum : y₁ + y₂ ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue (y₁ + y₂) hysum =
      concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
        concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂ := by
  calc
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue (y₁ + y₂) hysum
        = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
            (y₁ + y₂) (concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂) := by
            exact concrete_l2_r2_formal_adjoint_operator_value_proof_irrel
              (y₁ + y₂) hysum
              (concrete_l2_r2_formal_adjoint_domain_add hy₁ hy₂)
    _ = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₁ hy₁ +
        concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y₂ hy₂ := by
          exact concrete_l2_r2_formal_adjoint_operator_value_add hy₁ hy₂

/-- Homogeneity of the chosen formal-adjoint operator value for any supplied
proof that the scalar multiple lies in the formal-adjoint domain candidate. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_smul_of_domain
    (c : ℝ) {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate)
    (hcsmul : c • y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue (c • y) hcsmul =
      c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy := by
  calc
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue (c • y) hcsmul
        = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue
            (c • y) (concrete_l2_r2_formal_adjoint_domain_smul c hy) := by
            exact concrete_l2_r2_formal_adjoint_operator_value_proof_irrel
              (c • y) hcsmul
              (concrete_l2_r2_formal_adjoint_domain_smul c hy)
    _ = c • concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy := by
          exact concrete_l2_r2_formal_adjoint_operator_value_smul c hy

/-- The chosen formal-adjoint operator value promoted to a Mathlib `LinearMap`
from the formal-adjoint domain submodule into the ambient real `l2` Hilbert
space. -/
def concreteL2R2CompletedDiagonalFormalAdjointLinearMap :
    concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule →ₗ[ℝ]
      lp (fun _ : ℕ => ℝ) 2 where
  toFun y :=
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y.1 y.2
  map_add' := by
    intro y₁ y₂
    simpa using
      (concrete_l2_r2_formal_adjoint_operator_value_add_of_domain
        (hy₁ := y₁.2) (hy₂ := y₂.2)
        (hysum := (y₁ + y₂ :
          concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule).2))
  map_smul' := by
    intro c y
    simpa using
      (concrete_l2_r2_formal_adjoint_operator_value_smul_of_domain c
        (hy := y.2)
        (hcsmul := (c • y :
          concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule).2))

/-- Every point of the formal-adjoint domain submodule is mapped to a value whose
pair lies in the formal-adjoint graph candidate. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_mem
    (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) :
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  show
    ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
        inner ℝ (concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) z =
          inner ℝ y.1 Tz
  intro z Tz hzgraph
  have hmem :
      (y.1, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y.1 y.2) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
    exact concrete_l2_r2_formal_adjoint_operator_value_mem y.1 y.2
  exact hmem hzgraph

/-- Coordinate equation for the Mathlib `LinearMap` version of the formal-adjoint
operator value. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_coordinate_equation
    (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) (n : ℕ) :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMap y n =
      concreteL2DiagonalWeight n * y.1 n := by
  change
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y.1 y.2 n =
      concreteL2DiagonalWeight n * y.1 n
  exact concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation y.2 n

/-- The graph induced by the Mathlib `LinearMap` presentation of the formal
adjoint value. -/
def concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph :
    Set ConcreteL2R2PairSpace :=
  {p | ∃ y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule,
    p = (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y)}

/-- The Mathlib `LinearMap` graph is contained in the formal-adjoint graph
candidate. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_subset_candidate :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ⊆
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  intro p hp
  rcases hp with ⟨y, rfl⟩
  exact concrete_l2_r2_formal_adjoint_linear_map_graph_mem y

/-- The formal-adjoint graph candidate is contained in the graph induced by the
Mathlib `LinearMap` presentation. -/
theorem concrete_l2_r2_formal_adjoint_candidate_subset_linear_map_graph :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  intro p hp
  rcases p with ⟨y, w⟩
  have hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate := by
    exact ⟨w, hp⟩
  let yd : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule := ⟨y, hy⟩
  have hw : w = concreteL2R2CompletedDiagonalFormalAdjointLinearMap yd := by
    change w = concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy
    exact concrete_l2_r2_formal_adjoint_operator_value_unique (hy := hy) (hw := hp)
  refine ⟨yd, ?_⟩
  change (y, w) = (y, concreteL2R2CompletedDiagonalFormalAdjointLinearMap yd)
  rw [hw]

/-- The Mathlib `LinearMap` graph presentation is exactly the formal-adjoint graph
candidate. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact Set.Subset.antisymm
    concrete_l2_r2_formal_adjoint_linear_map_graph_subset_candidate
    concrete_l2_r2_formal_adjoint_candidate_subset_linear_map_graph

/-- The Mathlib `LinearMap` graph presentation also recovers the completed
diagonal graph carrier, using the already proved graph-level equality. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rw [concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate]
  exact concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate.symm

/-- Closedness of the Mathlib `LinearMap` graph presentation, transported from
the already proved closedness of the completed diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed :
    IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  rw [concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph]
  exact concrete_l2_r2_completed_diagonal_graph_isClosed

/-- Closedness of the formal-adjoint graph candidate, transported through the
Mathlib `LinearMap` graph presentation. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_isClosed :
    IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rw [← concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate]
  exact concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed

/-- Closedness of the graph presentation and the carrier equalities needed for the
next closed-operator handoff. -/
def concreteL2R2FormalAdjointLinearMapClosedGraphTransfer : Prop :=
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier

/-- The closed-graph transfer from the completed diagonal carrier to the
formal-adjoint `LinearMap` graph is complete. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_closed_graph_transfer_ready :
    concreteL2R2FormalAdjointLinearMapClosedGraphTransfer := by
  exact ⟨
    concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed,
    concrete_l2_r2_formal_adjoint_graph_candidate_isClosed,
    concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate,
    concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph⟩

/-- Type obligation closed by the Mathlib `Submodule` and `LinearMap` packaging
of the formal-adjoint graph-level operator value. -/
def concreteL2R2FormalAdjointSubmoduleLinearMapTypeObligation : Prop :=
  ((concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule :
      Set (lp (fun _ : ℕ => ℝ) 2)) =
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule,
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) (n : ℕ),
    concreteL2R2CompletedDiagonalFormalAdjointLinearMap y n =
      concreteL2DiagonalWeight n * y.1 n) ∧
  concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  concreteL2R2FormalAdjointLinearMapClosedGraphTransfer

/-- The formal-adjoint domain/value pair is now packaged as a Mathlib
`Submodule` plus `LinearMap`. -/
theorem concrete_l2_r2_formal_adjoint_submodule_linear_map_type_obligation_ready :
    concreteL2R2FormalAdjointSubmoduleLinearMapTypeObligation := by
  exact ⟨
    concrete_l2_r2_formal_adjoint_domain_submodule_carrier_eq,
    concrete_l2_r2_formal_adjoint_linear_map_graph_mem,
    concrete_l2_r2_formal_adjoint_linear_map_coordinate_equation,
    concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate,
    concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph,
    concrete_l2_r2_formal_adjoint_linear_map_closed_graph_transfer_ready⟩

/-- Readiness surface for the Mathlib-facing formal-adjoint submodule/linear-map
promotion.

This deliberately remains below Mathlib `adjoint`, `IsSelfAdjoint`, spectral
measure, PVM, and positive spectral weight. -/
def concreteAnalyticSpineL2R2FormalAdjointSubmoduleLinearMapReady : Prop :=
  concreteAnalyticSpineL2R2FormalAdjointOperatorValueSurfaceReady ∧
  concreteL2R2FormalAdjointSubmoduleLinearMapTypeObligation ∧
  True ∧ True ∧ True ∧ True

/-- The Mathlib-facing formal-adjoint submodule/linear-map surface is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_submodule_linear_map_ready :
    concreteAnalyticSpineL2R2FormalAdjointSubmoduleLinearMapReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_formal_adjoint_operator_value_surface_ready,
    concrete_l2_r2_formal_adjoint_submodule_linear_map_type_obligation_ready,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
