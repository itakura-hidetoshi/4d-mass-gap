import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2HilbertPairingSymmetryFromTsumRealizer

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Canonical abstract pairing obtained by applying a chosen candidate limit / sum
extractor to the finite coordinate pairing net.  This is the strongest theorem we
can promote before proving that the extractor is the Mathlib `tsum` induced by a
convergent coordinate series. -/
def concreteL2R2CanonicalAbstractPairing
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate) :
    ConcreteL2R2HilbertPairing :=
  fun u v => TsumCandidate (fun s : Finset ℕ => concreteL2R2FinitePairing s u v)

/-- The canonical abstract pairing realizes the left finite-net candidate by
unfolding definitions. -/
theorem concrete_l2_r2_canonical_abstract_pairing_realizes_left
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) :
    concreteL2R2CanonicalAbstractPairing TsumCandidate Tx z =
      concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz := by
  rfl

/-- The canonical abstract pairing realizes the right finite-net candidate by
unfolding definitions. -/
theorem concrete_l2_r2_canonical_abstract_pairing_realizes_right
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) :
    concreteL2R2CanonicalAbstractPairing TsumCandidate x Tz =
      concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz := by
  rfl

/-- The canonical abstract finite-net pairing is symmetric on the completed
diagonal graph.  This is no longer merely a conditional theorem with an external
realizer: the realizer is constructed by definitional unfolding of the canonical
pairing. -/
theorem concrete_l2_r2_canonical_abstract_pairing_symmetry
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    concreteL2R2CanonicalAbstractPairing TsumCandidate Tx z =
      concreteL2R2CanonicalAbstractPairing TsumCandidate x Tz := by
  exact
    concrete_l2_r2_hilbert_pairing_symmetry_from_realization_equalities
      TsumCandidate
      (concreteL2R2CanonicalAbstractPairing TsumCandidate)
      hxgraph
      hzgraph
      (concrete_l2_r2_canonical_abstract_pairing_realizes_left TsumCandidate x Tx z Tz)
      (concrete_l2_r2_canonical_abstract_pairing_realizes_right TsumCandidate x Tx z Tz)

/-- Route-level bridge recording that canonical abstract finite-net pairings are
already symmetric on the completed diagonal graph for every candidate extractor.
What remains is to identify a mathematically canonical extractor with `tsum` and
then with Mathlib's Hilbert inner product. -/
structure ConcreteL2R2CanonicalAbstractPairingSymmetryBridge where
  pairingSymmetryFromTsumRealizerBridgeReady :
    concreteAnalyticSpineL2R2HilbertPairingSymmetryFromTsumRealizerBridgeReady
  canonicalAbstractPairingSymmetry :
    ∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
      {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
      (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      concreteL2R2CanonicalAbstractPairing TsumCandidate Tx z =
        concreteL2R2CanonicalAbstractPairing TsumCandidate x Tz
  boundaryNotConcreteTsumExtractor : Prop
  boundaryNotHilbertInnerProductIdentification : Prop
  boundaryNotAdjointDomainAgreement : Prop
  boundaryNotSelfAdjointnessTheorem : Prop

/-- Concrete canonical abstract pairing symmetry bridge. -/
def concreteL2R2CanonicalAbstractPairingSymmetryBridge :
    ConcreteL2R2CanonicalAbstractPairingSymmetryBridge :=
  { pairingSymmetryFromTsumRealizerBridgeReady :=
      concrete_analytic_spine_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer_bridge_ready
    canonicalAbstractPairingSymmetry :=
      fun TsumCandidate x Tx z Tz hxgraph hzgraph =>
        concrete_l2_r2_canonical_abstract_pairing_symmetry TsumCandidate hxgraph hzgraph
    boundaryNotConcreteTsumExtractor := True
    boundaryNotHilbertInnerProductIdentification := True
    boundaryNotAdjointDomainAgreement := True
    boundaryNotSelfAdjointnessTheorem := True }

/-- Public ready predicate for canonical abstract pairing symmetry. -/
def concreteAnalyticSpineL2R2CanonicalAbstractPairingSymmetryBridgeReady : Prop :=
  concreteAnalyticSpineL2R2HilbertPairingSymmetryFromTsumRealizerBridgeReady ∧
  (∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    concreteL2R2CanonicalAbstractPairing TsumCandidate Tx z =
      concreteL2R2CanonicalAbstractPairing TsumCandidate x Tz) ∧
  True ∧ True ∧ True ∧ True

/-- The canonical abstract finite-net pairing symmetry bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_canonical_abstract_pairing_symmetry_bridge_ready :
    concreteAnalyticSpineL2R2CanonicalAbstractPairingSymmetryBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer_bridge_ready,
    fun TsumCandidate x Tx z Tz hxgraph hzgraph =>
      concrete_l2_r2_canonical_abstract_pairing_symmetry TsumCandidate hxgraph hzgraph,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
