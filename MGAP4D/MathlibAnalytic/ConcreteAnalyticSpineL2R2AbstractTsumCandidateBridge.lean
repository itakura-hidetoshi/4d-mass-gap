import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteNetLimitCompatibilityBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Abstract finite-net-to-sum candidate.  This is intentionally only a name for
an arbitrary extractor from finite coordinate nets to real numbers.  A later
analytic file may instantiate this extractor by `tsum`/`HasSum`, but this bridge
itself does not assert convergence. -/
abbrev ConcreteL2R2AbstractTsumCandidate := (Finset ℕ → ℝ) → ℝ

/-- Left abstract `tsum` candidate generated from the finite pairing net. -/
def concreteL2R2LeftAbstractTsumCandidate
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) : ℝ :=
  TsumCandidate (fun s : Finset ℕ => concreteL2R2LeftFinitePairingNet x Tx z Tz s)

/-- Right abstract `tsum` candidate generated from the finite pairing net. -/
def concreteL2R2RightAbstractTsumCandidate
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) : ℝ :=
  TsumCandidate (fun s : Finset ℕ => concreteL2R2RightFinitePairingNet x Tx z Tz s)

/-- Any abstract candidate that is a function of the finite net agrees on the two
sides, because the finite nets already agree pointwise.  This is still not a
`tsum` theorem; it is the named candidate-level equality surface used before the
actual summability/limit proof is supplied. -/
theorem concrete_l2_r2_abstract_tsum_candidates_agree
    (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz =
      concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz := by
  simpa [concreteL2R2LeftAbstractTsumCandidate, concreteL2R2RightAbstractTsumCandidate] using
    concrete_l2_r2_finite_net_extensional_limit_agree TsumCandidate hxgraph hzgraph

/-- Candidate-level bridge between finite-net equality and a future `tsum`
realization.  It promotes only abstract candidate equality; actual summability,
`HasSum`, `Summable`, and Hilbert inner-product identification remain explicit
boundary obligations. -/
structure ConcreteL2R2AbstractTsumCandidateBridge where
  finiteNetLimitCompatibilityBridgeReady :
    concreteAnalyticSpineL2R2FiniteNetLimitCompatibilityBridgeReady
  abstractTsumCandidatesAgree :
    ∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
      {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
      (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz =
        concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz
  boundaryNotHasSumTheorem : Prop
  boundaryNotSummableTheorem : Prop
  boundaryNotConcreteTsumTheorem : Prop
  boundaryNotHilbertInnerProductIdentification : Prop

/-- Concrete abstract `tsum` candidate bridge. -/
def concreteL2R2AbstractTsumCandidateBridge :
    ConcreteL2R2AbstractTsumCandidateBridge :=
  { finiteNetLimitCompatibilityBridgeReady :=
      concrete_analytic_spine_l2_r2_finite_net_limit_compatibility_bridge_ready
    abstractTsumCandidatesAgree :=
      fun TsumCandidate x Tx z Tz hxgraph hzgraph =>
        concrete_l2_r2_abstract_tsum_candidates_agree TsumCandidate hxgraph hzgraph
    boundaryNotHasSumTheorem := True
    boundaryNotSummableTheorem := True
    boundaryNotConcreteTsumTheorem := True
    boundaryNotHilbertInnerProductIdentification := True }

/-- Public ready predicate for the abstract `tsum` candidate bridge. -/
def concreteAnalyticSpineL2R2AbstractTsumCandidateBridgeReady : Prop :=
  concreteAnalyticSpineL2R2FiniteNetLimitCompatibilityBridgeReady ∧
  (∀ (TsumCandidate : ConcreteL2R2AbstractTsumCandidate)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    concreteL2R2LeftAbstractTsumCandidate TsumCandidate x Tx z Tz =
      concreteL2R2RightAbstractTsumCandidate TsumCandidate x Tx z Tz) ∧
  True ∧ True ∧ True ∧ True

/-- The abstract `tsum` candidate bridge is ready at the candidate-equality
level. -/
theorem concrete_analytic_spine_l2_r2_abstract_tsum_candidate_bridge_ready :
    concreteAnalyticSpineL2R2AbstractTsumCandidateBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_finite_net_limit_compatibility_bridge_ready,
    fun TsumCandidate x Tx z Tz hxgraph hzgraph =>
      concrete_l2_r2_abstract_tsum_candidates_agree TsumCandidate hxgraph hzgraph,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
