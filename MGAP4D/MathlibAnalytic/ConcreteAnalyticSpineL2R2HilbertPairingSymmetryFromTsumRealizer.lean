import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AbstractTsumCandidateBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A real-valued pairing on the concrete `lp` carrier.  This abstraction lets the
finite-net theorem promote directly to a symmetry theorem once a later analytic
file proves that the pairing is realized by the chosen finite-net/`tsum`
extractor. -/
abbrev ConcreteL2R2HilbertPairing :=
  lp (fun _ : ℕ => ℝ) 2 → lp (fun _ : ℕ => ℝ) 2 → ℝ

/-- Realization data saying that the chosen real pairing is obtained from the
left and right abstract `tsum` candidates on a given graph-pair square. -/
structure ConcreteL2R2PairingTsumRealizer
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (HilbertPairing : ConcreteL2R2HilbertPairing)
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) where
  realizesLeft :
    HilbertPairing Tx z = concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz
  realizesRight :
    HilbertPairing x Tz = concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz

/-- Main promoted theorem for this layer: once the analytic realization of the
pairing by the same abstract finite-net `tsum` candidate is supplied on both
sides, the completed diagonal graph is symmetric for that pairing.  No proof is
omitted: the proof is a direct equality chain using the already-proven finite-net
candidate equality. -/
theorem concrete_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (HilbertPairing : ConcreteL2R2HilbertPairing)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (realizer : ConcreteL2R2PairingTsumRealizer TsumCandidate HilbertPairing x Tx z Tz) :
    HilbertPairing Tx z = HilbertPairing x Tz := by
  calc
    HilbertPairing Tx z
        = concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz := realizer.realizesLeft
    _ = concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz :=
        concrete_l2_r2_abstract_tsum_candidates_agree TsumCandidate hxgraph hzgraph
    _ = HilbertPairing x Tz := realizer.realizesRight.symm

/-- A curried version that is easier for later route files to reuse with raw
realization equalities instead of an explicit realizer record. -/
theorem concrete_l2_r2_hilbert_pairing_symmetry_from_realization_equalities
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (HilbertPairing : ConcreteL2R2HilbertPairing)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hleft :
      HilbertPairing Tx z = concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz)
    (hright :
      HilbertPairing x Tz = concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz) :
    HilbertPairing Tx z = HilbertPairing x Tz := by
  exact
    concrete_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer
      TsumCandidate HilbertPairing hxgraph hzgraph
      { realizesLeft := hleft
        realizesRight := hright }

/-- This theorem-level bridge records the exact promotion obtained here: the
candidate-equality layer now yields a genuine pairing-symmetry theorem whenever
an analytic `tsum` realizer is available.  The construction of such a realizer
is intentionally not faked here. -/
structure ConcreteL2R2HilbertPairingSymmetryFromTsumRealizerBridge where
  abstractTsumCandidateBridgeReady :
    concreteAnalyticSpineL2R2AbstractTsumCandidateBridgeReady
  pairingSymmetryFromRealizer :
    ∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
      (HilbertPairing : ConcreteL2R2HilbertPairing)
      {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
      (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      ConcreteL2R2PairingTsumRealizer TsumCandidate HilbertPairing x Tx z Tz →
      HilbertPairing Tx z = HilbertPairing x Tz
  boundaryNotConcreteTsumRealizerConstructed : Prop
  boundaryNotAdjointDomainAgreement : Prop
  boundaryNotSelfAdjointnessTheorem : Prop

/-- Concrete bridge instance for the realizer-to-symmetry theorem. -/
def concreteL2R2HilbertPairingSymmetryFromTsumRealizerBridge :
    ConcreteL2R2HilbertPairingSymmetryFromTsumRealizerBridge :=
  { abstractTsumCandidateBridgeReady :=
      concrete_analytic_spine_l2_r2_abstract_tsum_candidate_bridge_ready
    pairingSymmetryFromRealizer :=
      fun TsumCandidate HilbertPairing x Tx z Tz hxgraph hzgraph realizer =>
        concrete_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer
          TsumCandidate HilbertPairing hxgraph hzgraph realizer
    boundaryNotConcreteTsumRealizerConstructed := True
    boundaryNotAdjointDomainAgreement := True
    boundaryNotSelfAdjointnessTheorem := True }

/-- Public ready predicate for the theorem-level pairing-symmetry bridge. -/
def concreteAnalyticSpineL2R2HilbertPairingSymmetryFromTsumRealizerBridgeReady : Prop :=
  concreteAnalyticSpineL2R2AbstractTsumCandidateBridgeReady ∧
  (∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (HilbertPairing : ConcreteL2R2HilbertPairing)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    ConcreteL2R2PairingTsumRealizer TsumCandidate HilbertPairing x Tx z Tz →
    HilbertPairing Tx z = HilbertPairing x Tz) ∧
  True ∧ True ∧ True

/-- The theorem-level pairing-symmetry bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer_bridge_ready :
    concreteAnalyticSpineL2R2HilbertPairingSymmetryFromTsumRealizerBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_abstract_tsum_candidate_bridge_ready,
    fun TsumCandidate HilbertPairing x Tx z Tz hxgraph hzgraph realizer =>
      concrete_l2_r2_hilbert_pairing_symmetry_from_tsum_realizer
        TsumCandidate HilbertPairing hxgraph hzgraph realizer,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
