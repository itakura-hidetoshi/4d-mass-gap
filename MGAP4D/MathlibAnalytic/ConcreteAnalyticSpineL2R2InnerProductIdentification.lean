import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateTsumPairingSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- In the one-dimensional real Hilbert space, Mathlib's real inner product is
ordinary multiplication.  The proof avoids relying on a fragile simp-normal form:
write both real numbers as scalar multiples of `1`, use real-linearity of the
inner product on both sides, and evaluate `inner ℝ 1 1` by the norm-square
identity. -/
theorem concrete_l2_r2_real_inner_eq_mul (a b : ℝ) :
    inner ℝ a b = a * b := by
  have h11 : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (1 : ℝ))
  calc
    inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
    _ = a * inner ℝ (1 : ℝ) (b • (1 : ℝ)) := by
      rw [real_inner_smul_left]
    _ = a * (b * inner ℝ (1 : ℝ) (1 : ℝ)) := by
      rw [real_inner_smul_right]
    _ = a * b := by
      rw [h11]
      ring

/-- The concrete coordinate `tsum` pairing is exactly Mathlib's real Hilbert
inner product on the `lp (fun _ : ℕ => ℝ) 2` carrier.  Mathlib's `lp.inner_eq_tsum`
reduces the Hilbert-sum inner product to the coordinate inner products; the
preceding scalar lemma identifies each real coordinate inner product with
ordinary multiplication. -/
theorem concrete_l2_r2_inner_eq_coordinate_tsum_pairing
    (u v : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ u v = concreteL2R2CoordinateTsumPairing u v := by
  rw [lp.inner_eq_tsum]
  unfold concreteL2R2CoordinateTsumPairing
  apply tsum_congr
  intro n
  exact concrete_l2_r2_real_inner_eq_mul (u n) (v n)

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
