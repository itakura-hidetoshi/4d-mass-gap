import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CanonicalAbstractPairingSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete coordinate `tsum` pairing on the real `lp` carrier.  This is the
first actual infinite-coordinate pairing promoted in this lane. -/
def concreteL2R2CoordinateTsumPairing
    (u v : lp (fun _ : ℕ => ℝ) 2) : ℝ :=
  ∑' n : ℕ, (u n) * (v n)

/-- The singleton-extractor turns a finite-net surface into the `tsum` of its
singleton increments.  For finite pairings this recovers the coordinate product
series. -/
def concreteL2R2SingletonTsumCandidate : ConcreteL2R2AbstractTsumCandidate :=
  fun F => ∑' n : ℕ, F ({n} : Finset ℕ)

/-- The canonical abstract pairing induced by the singleton extractor is exactly
the concrete coordinate `tsum` pairing. -/
theorem concrete_l2_r2_canonical_singleton_pairing_eq_coordinate_tsum_pairing
    (u v : lp (fun _ : ℕ => ℝ) 2) :
    concreteL2R2CanonicalAbstractPairing concreteL2R2SingletonTsumCandidate u v =
      concreteL2R2CoordinateTsumPairing u v := by
  simp [concreteL2R2CanonicalAbstractPairing,
    concreteL2R2SingletonTsumCandidate,
    concreteL2R2CoordinateTsumPairing,
    concreteL2R2FinitePairing]

/-- Concrete coordinate `tsum` pairing symmetry on the completed diagonal graph.
The proof is not an obligation packet: it instantiates the already-proved
canonical abstract pairing symmetry with the singleton `tsum` extractor and then
identifies that canonical pairing with the concrete coordinate `tsum` pairing. -/
theorem concrete_l2_r2_coordinate_tsum_pairing_graph_symmetry
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    concreteL2R2CoordinateTsumPairing Tx z =
      concreteL2R2CoordinateTsumPairing x Tz := by
  calc
    concreteL2R2CoordinateTsumPairing Tx z
        = concreteL2R2CanonicalAbstractPairing concreteL2R2SingletonTsumCandidate Tx z :=
          (concrete_l2_r2_canonical_singleton_pairing_eq_coordinate_tsum_pairing Tx z).symm
    _ = concreteL2R2CanonicalAbstractPairing concreteL2R2SingletonTsumCandidate x Tz :=
          concrete_l2_r2_canonical_abstract_pairing_symmetry
            concreteL2R2SingletonTsumCandidate hxgraph hzgraph
    _ = concreteL2R2CoordinateTsumPairing x Tz :=
          concrete_l2_r2_canonical_singleton_pairing_eq_coordinate_tsum_pairing x Tz

/-- Direct commutativity of the concrete coordinate `tsum` pairing.  This is
separate from graph symmetry and follows pointwise from commutativity of real
multiplication. -/
theorem concrete_l2_r2_coordinate_tsum_pairing_comm
    (u v : lp (fun _ : ℕ => ℝ) 2) :
    concreteL2R2CoordinateTsumPairing u v =
      concreteL2R2CoordinateTsumPairing v u := by
  unfold concreteL2R2CoordinateTsumPairing
  apply tsum_congr
  intro n
  ring

/-- Public ready predicate for concrete coordinate `tsum` pairing symmetry on the
completed diagonal graph. -/
def concreteAnalyticSpineL2R2CoordinateTsumPairingSymmetryReady : Prop :=
  concreteAnalyticSpineL2R2CanonicalAbstractPairingSymmetryBridgeReady ∧
  (∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    concreteL2R2CoordinateTsumPairing Tx z =
      concreteL2R2CoordinateTsumPairing x Tz) ∧
  (∀ u v : lp (fun _ : ℕ => ℝ) 2,
    concreteL2R2CoordinateTsumPairing u v =
      concreteL2R2CoordinateTsumPairing v u)

/-- The concrete coordinate `tsum` pairing symmetry layer is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_tsum_pairing_symmetry_ready :
    concreteAnalyticSpineL2R2CoordinateTsumPairingSymmetryReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_canonical_abstract_pairing_symmetry_bridge_ready,
    fun x Tx z Tz hxgraph hzgraph =>
      concrete_l2_r2_coordinate_tsum_pairing_graph_symmetry hxgraph hzgraph,
    concrete_l2_r2_coordinate_tsum_pairing_comm⟩

end

end MathlibAnalytic
end MGAP4D
