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

/-- Reverse-containment coordinate extraction packet.

This does not yet claim reverse containment as set membership in the original
graph carrier.  It records the exact coordinate equation that any formal-adjoint
candidate witness must satisfy. -/
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
  boundaryNotReverseContainmentTheorem : Prop
  boundaryNotDomainAgreementTheorem : Prop
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
    boundaryNotReverseContainmentTheorem := True
    boundaryNotDomainAgreementTheorem := True
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
  True ∧ True ∧ True ∧ True

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
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
