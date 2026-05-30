import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalFiniteCoordinateSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Finite coordinate pairing used as the finite-partial-sum surface before
passing to any infinite Hilbert inner product or `tsum` statement. -/
def concreteL2R2FinitePairing
    (s : Finset ℕ) (u v : lp (fun _ : ℕ => ℝ) 2) : ℝ :=
  Finset.sum s (fun n => (u n) * (v n))

/-- Finite graph symmetry restated through the finite-pairing surface.  This is
still a finite-coordinate theorem, not yet an infinite inner-product theorem. -/
theorem concrete_l2_r2_completed_diagonal_operator_finite_pairing_symmetry
    (s : Finset ℕ)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    concreteL2R2FinitePairing s Tx z = concreteL2R2FinitePairing s x Tz := by
  simpa [concreteL2R2FinitePairing] using
    concrete_l2_r2_completed_diagonal_operator_finite_coordinate_symmetry s hxgraph hzgraph

/-- A small record documenting exactly what has been promoted at this stage:
finite partial pairings are symmetric on graph pairs, while infinite summability
and Hilbert inner-product symmetry remain separate downstream obligations. -/
structure ConcreteL2R2FinitePairingSummabilityBridge where
  finiteCoordinateSymmetryReady : concreteAnalyticSpineL2R2DiagonalFiniteCoordinateSymmetryReady
  finitePairingSymmetry :
    ∀ s : Finset ℕ, ∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
      (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      concreteL2R2FinitePairing s Tx z = concreteL2R2FinitePairing s x Tz
  boundaryNotTsumPassage : Prop
  boundaryNotHilbertInnerProductSymmetry : Prop
  boundaryNotAdjointDomainAgreement : Prop

/-- Concrete bridge object for the finite-pairing layer. -/
def concreteL2R2FinitePairingSummabilityBridge :
    ConcreteL2R2FinitePairingSummabilityBridge :=
  { finiteCoordinateSymmetryReady :=
      concrete_analytic_spine_l2_r2_diagonal_finite_coordinate_symmetry_ready
    finitePairingSymmetry :=
      fun s x Tx z Tz hxgraph hzgraph =>
        concrete_l2_r2_completed_diagonal_operator_finite_pairing_symmetry s hxgraph hzgraph
    boundaryNotTsumPassage := True
    boundaryNotHilbertInnerProductSymmetry := True
    boundaryNotAdjointDomainAgreement := True }

/-- Public theorem-entry predicate for the finite-pairing summability bridge. -/
def concreteAnalyticSpineL2R2FinitePairingSummabilityBridgeReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalFiniteCoordinateSymmetryReady ∧
  (∀ s : Finset ℕ, ∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    concreteL2R2FinitePairing s Tx z = concreteL2R2FinitePairing s x Tz) ∧
  True ∧ True ∧ True

/-- The finite-pairing summability bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_finite_pairing_summability_bridge_ready :
    concreteAnalyticSpineL2R2FinitePairingSummabilityBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_diagonal_finite_coordinate_symmetry_ready,
    fun s x Tx z Tz hxgraph hzgraph =>
      concrete_l2_r2_completed_diagonal_operator_finite_pairing_symmetry s hxgraph hzgraph,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
