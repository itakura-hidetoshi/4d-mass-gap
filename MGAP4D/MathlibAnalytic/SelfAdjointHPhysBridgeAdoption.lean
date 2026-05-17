import MGAP4D.MathlibAnalytic.HilbertToPhysicalUnboundedOperatorBridge
import MGAP4D.MathlibAnalytic.SelfAdjointHPhysLaneHardening

namespace MGAP4D
namespace MathlibAnalytic

/-- Adoption surface showing that the self-adjoint `H_phys` hardening lane can
read its physical unbounded-operator component through the hardened
Hilbert-to-physical bridge.

This is additive: the installed lane is not rewritten, but the proof surface now
has a named route

`HilbertConstructionLaneHardening → HilbertToPhysicalUnboundedOperatorBridge
 → SelfAdjointHPhysLaneHardening`.
-/
structure SelfAdjointHPhysBridgeAdoptionData where
  hilbertToPhysicalBridgeReady : hilbertToPhysicalUnboundedOperatorBridgeData.ready
  selfAdjointLaneReady : selfAdjointHPhysLaneHardeningData.ready
  bridgeOperatorReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  laneOperatorReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  lanePhysicalOperatorHardened : selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened
  bridgeSelfAdjointCertificate : physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate
  bridgeRayleighLowerBound : physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound
  laneSelfAdjointCertificateHardened : selfAdjointHPhysLaneHardeningData.selfAdjointCertificateHardened
  laneRayleighCompatibilityHardened : selfAdjointHPhysLaneHardeningData.rayleighCompatibilityHardened
  exactValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  bridgeAdoptedByLane : Prop
  bridgeAdoptedByLane_proof : bridgeAdoptedByLane
  downstreamConcreteHPhysBridgeReady : concreteHPhysRealizationTheoremReviewSurface.ready
  concreteYangMillsHamiltonianStillOpen : physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen
  spectralRealizationStillOpen : physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen
  publicBoundaryHeld : selfAdjointHPhysLaneHardeningData.publicBoundaryHeld
  finalReleaseHeld : selfAdjointHPhysLaneHardeningData.finalReleaseHeld

/-- Ready predicate for the bridge-adoption surface. -/
def SelfAdjointHPhysBridgeAdoptionData.ready
    (D : SelfAdjointHPhysBridgeAdoptionData) : Prop :=
  hilbertToPhysicalUnboundedOperatorBridgeData.ready ∧
  selfAdjointHPhysLaneHardeningData.ready ∧
  physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
  selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened ∧
  physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate ∧
  physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound ∧
  selfAdjointHPhysLaneHardeningData.selfAdjointCertificateHardened ∧
  selfAdjointHPhysLaneHardeningData.rayleighCompatibilityHardened ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.bridgeAdoptedByLane ∧
  concreteHPhysRealizationTheoremReviewSurface.ready ∧
  physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen ∧
  physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen ∧
  selfAdjointHPhysLaneHardeningData.publicBoundaryHeld ∧
  selfAdjointHPhysLaneHardeningData.finalReleaseHeld

/-- The self-adjoint lane can read the physical operator through the bridge. -/
theorem self_adjoint_hphys_bridge_adoption_operator_ready
    (D : SelfAdjointHPhysBridgeAdoptionData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.ready := by
  exact D.bridgeOperatorReady

/-- The physical operator hardening in the lane is paired with bridge readiness. -/
theorem self_adjoint_hphys_bridge_adoption_operator_hardened
    (D : SelfAdjointHPhysBridgeAdoptionData) (_hD : D.ready) :
    selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened := by
  exact D.lanePhysicalOperatorHardened

/-- The bridge carries the self-adjoint certificate required by the lane. -/
theorem self_adjoint_hphys_bridge_adoption_self_adjoint_certificate
    (D : SelfAdjointHPhysBridgeAdoptionData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate := by
  exact D.bridgeSelfAdjointCertificate

/-- The bridge carries the Rayleigh lower bound required by the lane. -/
theorem self_adjoint_hphys_bridge_adoption_rayleigh_lower_bound
    (D : SelfAdjointHPhysBridgeAdoptionData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound := by
  exact D.bridgeRayleighLowerBound

/-- Exact normalized value remains fixed across bridge adoption. -/
theorem self_adjoint_hphys_bridge_adoption_exact_value
    (D : SelfAdjointHPhysBridgeAdoptionData) (_hD : D.ready) :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact D.exactValuePreserved

/-- Installed bridge-adoption surface for self-adjoint `H_phys`. -/
def selfAdjointHPhysBridgeAdoptionData : SelfAdjointHPhysBridgeAdoptionData :=
  { hilbertToPhysicalBridgeReady := hilbert_to_physical_unbounded_operator_bridge_ready
    selfAdjointLaneReady := self_adjoint_hphys_lane_hardening_ready
    bridgeOperatorReady := hilbertToPhysicalUnboundedOperatorBridgeData.physicalOperatorReady
    laneOperatorReady := selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonReady
    lanePhysicalOperatorHardened := selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened
    bridgeSelfAdjointCertificate :=
      hilbertToPhysicalUnboundedOperatorBridgeData.selfAdjointCertificate
    bridgeRayleighLowerBound := hilbertToPhysicalUnboundedOperatorBridgeData.rayleighLowerBound
    laneSelfAdjointCertificateHardened :=
      selfAdjointHPhysLaneHardeningData.selfAdjointCertificateHardened
    laneRayleighCompatibilityHardened :=
      selfAdjointHPhysLaneHardeningData.rayleighCompatibilityHardened
    exactValuePreserved := selfAdjointHPhysLaneHardeningData.exactValuePreserved
    bridgeAdoptedByLane :=
      hilbertToPhysicalUnboundedOperatorBridgeData.ready ∧
      selfAdjointHPhysLaneHardeningData.ready ∧
      physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
      selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened
    bridgeAdoptedByLane_proof :=
      And.intro hilbert_to_physical_unbounded_operator_bridge_ready <|
        And.intro self_adjoint_hphys_lane_hardening_ready <|
          And.intro hilbertToPhysicalUnboundedOperatorBridgeData.physicalOperatorReady
            selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonHardened
    downstreamConcreteHPhysBridgeReady :=
      selfAdjointHPhysLaneHardeningData.concreteHPhysBridgeReady
    concreteYangMillsHamiltonianStillOpen :=
      hilbertToPhysicalUnboundedOperatorBridgeData.concreteYangMillsHamiltonianStillOpen
    spectralRealizationStillOpen :=
      hilbertToPhysicalUnboundedOperatorBridgeData.spectralRealizationStillOpen
    publicBoundaryHeld := selfAdjointHPhysLaneHardeningData.publicBoundaryHeld
    finalReleaseHeld := selfAdjointHPhysLaneHardeningData.finalReleaseHeld }

/-- The installed self-adjoint `H_phys` bridge-adoption surface is ready. -/
theorem self_adjoint_hphys_bridge_adoption_ready :
    selfAdjointHPhysBridgeAdoptionData.ready selfAdjointHPhysBridgeAdoptionData := by
  exact And.intro selfAdjointHPhysBridgeAdoptionData.hilbertToPhysicalBridgeReady <|
    And.intro selfAdjointHPhysBridgeAdoptionData.selfAdjointLaneReady <|
    And.intro selfAdjointHPhysBridgeAdoptionData.bridgeOperatorReady <|
    And.intro selfAdjointHPhysBridgeAdoptionData.lanePhysicalOperatorHardened <|
    And.intro selfAdjointHPhysBridgeAdoptionData.bridgeSelfAdjointCertificate <|
    And.intro selfAdjointHPhysBridgeAdoptionData.bridgeRayleighLowerBound <|
    And.intro selfAdjointHPhysBridgeAdoptionData.laneSelfAdjointCertificateHardened <|
    And.intro selfAdjointHPhysBridgeAdoptionData.laneRayleighCompatibilityHardened <|
    And.intro selfAdjointHPhysBridgeAdoptionData.exactValuePreserved <|
    And.intro selfAdjointHPhysBridgeAdoptionData.bridgeAdoptedByLane_proof <|
    And.intro selfAdjointHPhysBridgeAdoptionData.downstreamConcreteHPhysBridgeReady <|
    And.intro selfAdjointHPhysBridgeAdoptionData.concreteYangMillsHamiltonianStillOpen <|
    And.intro selfAdjointHPhysBridgeAdoptionData.spectralRealizationStillOpen <|
    And.intro selfAdjointHPhysBridgeAdoptionData.publicBoundaryHeld
      selfAdjointHPhysBridgeAdoptionData.finalReleaseHeld

end MathlibAnalytic
end MGAP4D
