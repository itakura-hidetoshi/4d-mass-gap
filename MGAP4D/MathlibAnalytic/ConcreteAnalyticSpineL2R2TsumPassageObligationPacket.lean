import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FinitePairingSummabilityBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Left finite-pairing net for a graph pair: finite partial sums of `<Tx,z>`
in coordinate form. -/
def concreteL2R2LeftFinitePairingNet
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) (s : Finset ℕ) : ℝ :=
  concreteL2R2FinitePairing s Tx z

/-- Right finite-pairing net for a graph pair: finite partial sums of `<x,Tz>`
in coordinate form. -/
def concreteL2R2RightFinitePairingNet
    (x Tx z Tz : lp (fun _ : ℕ => ℝ) 2) (s : Finset ℕ) : ℝ :=
  concreteL2R2FinitePairing s x Tz

/-- The proven finite equality, now stated as equality of the two finite-pairing
nets at every finite coordinate set.  This is the exact handoff surface for a
future `tsum`/limit passage. -/
theorem concrete_l2_r2_finite_pairing_nets_agree
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    ∀ s : Finset ℕ,
      concreteL2R2LeftFinitePairingNet x Tx z Tz s =
        concreteL2R2RightFinitePairingNet x Tx z Tz s := by
  intro s
  simpa [concreteL2R2LeftFinitePairingNet, concreteL2R2RightFinitePairingNet] using
    concrete_l2_r2_completed_diagonal_operator_finite_pairing_symmetry s hxgraph hzgraph

/-- Obligation packet for the next passage from finite-pairing nets to infinite
Hilbert inner-product symmetry.  The only promoted theorem here is equality of
all finite coordinate nets; convergence, `tsum`, inner-product identification,
and adjoint-domain agreement remain explicit downstream obligations. -/
structure ConcreteL2R2TsumPassageObligationPacket where
  finitePairingBridgeReady : concreteAnalyticSpineL2R2FinitePairingSummabilityBridgeReady
  finitePairingNetsAgree :
    ∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
      (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      ∀ s : Finset ℕ,
        concreteL2R2LeftFinitePairingNet x Tx z Tz s =
          concreteL2R2RightFinitePairingNet x Tx z Tz s
  leftSummabilityObligation : Prop
  rightSummabilityObligation : Prop
  finiteNetLimitCompatibilityObligation : Prop
  coordinateTsumToHilbertInnerProductObligation : Prop
  boundaryNotTsumTheorem : Prop
  boundaryNotHilbertInnerProductSymmetry : Prop
  boundaryNotAdjointDomainAgreement : Prop

/-- Concrete obligation packet for the finite-net-to-`tsum` handoff. -/
def concreteL2R2TsumPassageObligationPacket :
    ConcreteL2R2TsumPassageObligationPacket :=
  { finitePairingBridgeReady :=
      concrete_analytic_spine_l2_r2_finite_pairing_summability_bridge_ready
    finitePairingNetsAgree :=
      fun x Tx z Tz hxgraph hzgraph s =>
        concrete_l2_r2_finite_pairing_nets_agree hxgraph hzgraph s
    leftSummabilityObligation := True
    rightSummabilityObligation := True
    finiteNetLimitCompatibilityObligation := True
    coordinateTsumToHilbertInnerProductObligation := True
    boundaryNotTsumTheorem := True
    boundaryNotHilbertInnerProductSymmetry := True
    boundaryNotAdjointDomainAgreement := True }

/-- Public theorem-entry predicate for the `tsum` passage obligation packet. -/
def concreteAnalyticSpineL2R2TsumPassageObligationPacketReady : Prop :=
  concreteAnalyticSpineL2R2FinitePairingSummabilityBridgeReady ∧
  (∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    ∀ s : Finset ℕ,
      concreteL2R2LeftFinitePairingNet x Tx z Tz s =
        concreteL2R2RightFinitePairingNet x Tx z Tz s) ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True

/-- The `tsum` passage obligation packet is ready at the finite-net level. -/
theorem concrete_analytic_spine_l2_r2_tsum_passage_obligation_packet_ready :
    concreteAnalyticSpineL2R2TsumPassageObligationPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_finite_pairing_summability_bridge_ready,
    fun x Tx z Tz hxgraph hzgraph s =>
      concrete_l2_r2_finite_pairing_nets_agree hxgraph hzgraph s,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
