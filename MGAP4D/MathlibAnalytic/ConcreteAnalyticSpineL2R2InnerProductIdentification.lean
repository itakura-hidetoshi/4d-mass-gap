import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateTsumPairingSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete coordinate `tsum` pairing is exactly Mathlib's real Hilbert
inner product on the `lp (fun _ : ℕ => ℝ) 2` carrier.  Mathlib's `lp.inner_eq_tsum`
reduces the Hilbert-sum inner product to the coordinate inner products, and the
coordinate inner product on `ℝ` reduces to multiplication. -/
theorem concrete_l2_r2_inner_eq_coordinate_tsum_pairing
    (u v : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ u v = concreteL2R2CoordinateTsumPairing u v := by
  rw [lp.inner_eq_tsum]
  unfold concreteL2R2CoordinateTsumPairing
  apply tsum_congr
  intro n
  simp

/-- The completed diagonal graph is symmetric for Mathlib's real Hilbert inner
product.  This is the actual inner-product symmetry layer obtained by combining
coordinate `tsum` graph symmetry with the preceding identification theorem. -/
theorem concrete_l2_r2_inner_product_graph_symmetry
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    inner ℝ Tx z = inner ℝ x Tz := by
  calc
    inner ℝ Tx z
        = concreteL2R2CoordinateTsumPairing Tx z :=
          concrete_l2_r2_inner_eq_coordinate_tsum_pairing Tx z
    _ = concreteL2R2CoordinateTsumPairing x Tz :=
          concrete_l2_r2_coordinate_tsum_pairing_graph_symmetry hxgraph hzgraph
    _ = inner ℝ x Tz :=
          (concrete_l2_r2_inner_eq_coordinate_tsum_pairing x Tz).symm

/-- Mathlib's real Hilbert inner product on this carrier is symmetric.  This is
kept as a direct exported theorem because it is useful for subsequent adjoint
surface work over `ℝ`. -/
theorem concrete_l2_r2_inner_product_comm
    (u v : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ u v = inner ℝ v u := by
  calc
    inner ℝ u v
        = concreteL2R2CoordinateTsumPairing u v :=
          concrete_l2_r2_inner_eq_coordinate_tsum_pairing u v
    _ = concreteL2R2CoordinateTsumPairing v u :=
          concrete_l2_r2_coordinate_tsum_pairing_comm u v
    _ = inner ℝ v u :=
          (concrete_l2_r2_inner_eq_coordinate_tsum_pairing v u).symm

/-- Public ready predicate for the Mathlib inner-product identification and graph
symmetry layer. -/
def concreteAnalyticSpineL2R2InnerProductIdentificationReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateTsumPairingSymmetryReady ∧
  (∀ u v : lp (fun _ : ℕ => ℝ) 2,
    inner ℝ u v = concreteL2R2CoordinateTsumPairing u v) ∧
  (∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    inner ℝ Tx z = inner ℝ x Tz) ∧
  (∀ u v : lp (fun _ : ℕ => ℝ) 2,
    inner ℝ u v = inner ℝ v u)

/-- The Mathlib inner-product identification layer is ready. -/
theorem concrete_analytic_spine_l2_r2_inner_product_identification_ready :
    concreteAnalyticSpineL2R2InnerProductIdentificationReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_tsum_pairing_symmetry_ready,
    concrete_l2_r2_inner_eq_coordinate_tsum_pairing,
    fun x Tx z Tz hxgraph hzgraph =>
      concrete_l2_r2_inner_product_graph_symmetry hxgraph hzgraph,
    concrete_l2_r2_inner_product_comm⟩

end

end MathlibAnalytic
end MGAP4D
