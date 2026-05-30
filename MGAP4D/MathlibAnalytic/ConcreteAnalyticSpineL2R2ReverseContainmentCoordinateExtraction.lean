import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A formal-adjoint witness satisfies the diagonal coordinate equation at every
coordinate.  This is the coordinate-extraction form needed before reverse graph
containment. -/
def concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation
    (y w : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  ∀ n : ℕ, w n = concreteL2DiagonalWeight n * y n

/-- Extract the diagonal coordinate equation from a formal-adjoint graph witness. -/
theorem concrete_l2_r2_formal_adjoint_witness_satisfies_diagonal_coordinate_equation
    {y w : lp (fun _ : ℕ => ℝ) 2}
    (hw : (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y w := by
  intro n
  exact concrete_l2_r2_formal_adjoint_candidate_coordinate_equation hw n

/-- The chosen formal-adjoint operator value satisfies the diagonal coordinate
equation at every coordinate. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_satisfies_diagonal_coordinate_equation
    {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y
      (concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) := by
  intro n
  exact concrete_l2_r2_formal_adjoint_operator_value_coordinate_equation hy n

/-- A formal-adjoint graph witness is already a point of the completed diagonal
graph carrier.  This is the reverse-containment step obtained from coordinate
extraction, not a Mathlib `adjoint` promotion. -/
theorem concrete_l2_r2_formal_adjoint_witness_mem_completed_diagonal_graph
    {y w : lp (fun _ : ℕ => ℝ) 2}
    (hw : (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) :
    (y, w) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  exact concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph hw

/-- Reverse-containment coordinate extraction packet.

This packet now includes the theorem-level bridge from the coordinate equation to
reverse graph containment.  It still does not identify the graph-level construction
with Mathlib's `adjoint` or promote graph equality to Mathlib `IsSelfAdjoint`. -/
structure ConcreteL2R2ReverseContainmentCoordinateExtractionPacket where
  mathlibOperatorTypeObligationReady :
    concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady
  formalAdjointWitnessCoordinateExtraction :
    ∀ {y w : lp (fun _ : ℕ => ℝ) 2},
      (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
      concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y w
  formalAdjointOperatorValueCoordinateExtraction :
    ∀ {y : lp (fun _ : ℕ => ℝ) 2},
      (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) →
      concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y
        (concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy)
  reverseGraphContainmentFromCoordinateExtraction :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier
  graphLevelAdjointEquality :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate
  boundaryNotMathlibAdjointPromotion : Prop
  boundaryNotMathlibIsSelfAdjointPromotion : Prop

/-- Concrete reverse-containment coordinate extraction packet. -/
def concreteL2R2ReverseContainmentCoordinateExtractionPacket :
    ConcreteL2R2ReverseContainmentCoordinateExtractionPacket :=
  { mathlibOperatorTypeObligationReady :=
      concrete_analytic_spine_l2_r2_mathlib_operator_type_obligation_packet_ready
    formalAdjointWitnessCoordinateExtraction := by
      intro y w hw
      exact concrete_l2_r2_formal_adjoint_witness_satisfies_diagonal_coordinate_equation hw
    formalAdjointOperatorValueCoordinateExtraction := by
      intro y hy
      exact concrete_l2_r2_formal_adjoint_operator_value_satisfies_diagonal_coordinate_equation hy
    reverseGraphContainmentFromCoordinateExtraction :=
      concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph
    graphLevelAdjointEquality :=
      concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate
    boundaryNotMathlibAdjointPromotion := True
    boundaryNotMathlibIsSelfAdjointPromotion := True }

/-- Public readiness predicate for reverse-containment coordinate extraction. -/
def concreteAnalyticSpineL2R2ReverseContainmentCoordinateExtractionPacketReady : Prop :=
  concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady ∧
  (∀ {y w : lp (fun _ : ℕ => ℝ) 2},
    (y, w) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y w) ∧
  (∀ {y : lp (fun _ : ℕ => ℝ) 2},
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) →
    concreteL2R2FormalAdjointWitnessSatisfiesDiagonalCoordinateEquation y
      (concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy)) ∧
  concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  True ∧ True

/-- The reverse-containment coordinate extraction packet is ready. -/
theorem concrete_analytic_spine_l2_r2_reverse_containment_coordinate_extraction_packet_ready :
    concreteAnalyticSpineL2R2ReverseContainmentCoordinateExtractionPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_mathlib_operator_type_obligation_packet_ready,
    (by
      intro y w hw
      exact concrete_l2_r2_formal_adjoint_witness_satisfies_diagonal_coordinate_equation hw),
    (by
      intro y hy
      exact concrete_l2_r2_formal_adjoint_operator_value_satisfies_diagonal_coordinate_equation hy),
    concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph,
    concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
