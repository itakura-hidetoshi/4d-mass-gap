import MGAP4D.MathlibAnalytic.CompleteInfiniteDimensionalHilbertConstruction
import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton

namespace MGAP4D
namespace MathlibAnalytic

/-- Bridge surface from the complete infinite-dimensional Hilbert construction
lane to the physical unbounded-operator skeleton.

This is additive: it does not claim a new concrete Yang--Mills Hamiltonian or a
closed spectral realization.  It records that the upstream complete Hilbert
construction lane and the downstream physical unbounded-operator skeleton are
simultaneously available, with the exact normalized value and the public/final
boundary flags preserved. -/
structure HilbertToPhysicalUnboundedOperatorBridgeData where
  hilbertLaneReady : completeInfiniteDimensionalHilbertConstructionLaneData.ready
  hilbertInstanceHardened : completeInfiniteDimensionalHilbertConstructionLaneData.hilbertInstanceHardened
  exactValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  physicalOperatorReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  domainPreserved : physicalUnboundedOperatorSkeletonReviewSurface.domainPreserved
  symmetricOnDomain : physicalUnboundedOperatorSkeletonReviewSurface.symmetricOnDomain
  selfAdjointCertificate : physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate
  rayleighLowerBound : physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound
  distinguishedAttainsExact : physicalUnboundedOperatorSkeletonReviewSurface.distinguishedAttainsExact
  bridgeEstablished : Prop
  bridgeEstablished_proof : bridgeEstablished
  concreteYangMillsHamiltonianStillOpen : physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen
  spectralRealizationStillOpen : physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen
  publicBoundaryHeld : physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld
  finalReleaseHeld : physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld

/-- Ready predicate for the Hilbert-to-physical unbounded-operator bridge. -/
def HilbertToPhysicalUnboundedOperatorBridgeData.ready
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) : Prop :=
  completeInfiniteDimensionalHilbertConstructionLaneData.ready ∧
  completeInfiniteDimensionalHilbertConstructionLaneData.hilbertInstanceHardened ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
  physicalUnboundedOperatorSkeletonReviewSurface.domainPreserved ∧
  physicalUnboundedOperatorSkeletonReviewSurface.symmetricOnDomain ∧
  physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate ∧
  physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound ∧
  physicalUnboundedOperatorSkeletonReviewSurface.distinguishedAttainsExact ∧
  D.bridgeEstablished ∧
  physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen ∧
  physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen ∧
  physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld ∧
  physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld

/-- The bridge preserves the upstream hardened Hilbert-instance witness. -/
theorem hilbert_to_physical_bridge_hilbert_instance_hardened
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    completeInfiniteDimensionalHilbertConstructionLaneData.hilbertInstanceHardened := by
  exact D.hilbertInstanceHardened

/-- The bridge exposes the downstream physical unbounded-operator readiness. -/
theorem hilbert_to_physical_bridge_operator_ready
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.ready := by
  exact D.physicalOperatorReady

/-- The bridge keeps the exact normalized gap value visible. -/
theorem hilbert_to_physical_bridge_exact_value_preserved
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact D.exactValuePreserved

/-- The bridge carries domain preservation for the physical operator. -/
theorem hilbert_to_physical_bridge_domain_preserved
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.domainPreserved := by
  exact D.domainPreserved

/-- The bridge carries symmetry on the declared physical domain. -/
theorem hilbert_to_physical_bridge_symmetric_on_domain
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.symmetricOnDomain := by
  exact D.symmetricOnDomain

/-- The bridge carries the physical self-adjoint certificate surface. -/
theorem hilbert_to_physical_bridge_self_adjoint_certificate
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate := by
  exact D.selfAdjointCertificate

/-- The bridge carries the Rayleigh lower-bound surface. -/
theorem hilbert_to_physical_bridge_rayleigh_lower_bound
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound := by
  exact D.rayleighLowerBound

/-- The bridge carries exact attainment by the distinguished state. -/
theorem hilbert_to_physical_bridge_distinguished_attains_exact
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.distinguishedAttainsExact := by
  exact D.distinguishedAttainsExact

/-- The bridge keeps the Yang--Mills Hamiltonian realization as an explicit
open downstream boundary. -/
theorem hilbert_to_physical_bridge_concrete_ym_still_open
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen := by
  exact D.concreteYangMillsHamiltonianStillOpen

/-- The bridge keeps the spectral realization as an explicit open downstream
boundary. -/
theorem hilbert_to_physical_bridge_spectral_realization_still_open
    (D : HilbertToPhysicalUnboundedOperatorBridgeData) (_hD : D.ready) :
    physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen := by
  exact D.spectralRealizationStillOpen

/-- Installed bridge from the complete infinite-dimensional Hilbert construction
lane to the physical unbounded-operator skeleton. -/
def hilbertToPhysicalUnboundedOperatorBridgeData :
    HilbertToPhysicalUnboundedOperatorBridgeData :=
  { hilbertLaneReady := complete_infinite_dimensional_hilbert_construction_lane_ready
    hilbertInstanceHardened :=
      complete_hilbert_construction_hilbert_instance_hardened
        completeInfiniteDimensionalHilbertConstructionLaneData
        complete_infinite_dimensional_hilbert_construction_lane_ready
    exactValuePreserved := completeInfiniteDimensionalHilbertConstructionLaneData.exactValuePreserved
    physicalOperatorReady := physical_unbounded_operator_skeleton_review_surface_ready
    domainPreserved := physicalUnboundedOperatorSkeletonReviewSurface.domainPreserved_proof
    symmetricOnDomain := physicalUnboundedOperatorSkeletonReviewSurface.symmetricOnDomain_proof
    selfAdjointCertificate := physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate_proof
    rayleighLowerBound := physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound_proof
    distinguishedAttainsExact :=
      physicalUnboundedOperatorSkeletonReviewSurface.distinguishedAttainsExact_proof
    bridgeEstablished :=
      completeInfiniteDimensionalHilbertConstructionLaneData.ready ∧
      physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20
    bridgeEstablished_proof :=
      And.intro complete_infinite_dimensional_hilbert_construction_lane_ready <|
        And.intro physical_unbounded_operator_skeleton_review_surface_ready
          completeInfiniteDimensionalHilbertConstructionLaneData.exactValuePreserved
    concreteYangMillsHamiltonianStillOpen :=
      physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen_proof
    spectralRealizationStillOpen :=
      physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen_proof
    publicBoundaryHeld := physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld_proof
    finalReleaseHeld := physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld_proof }

/-- The installed Hilbert-to-physical unbounded-operator bridge is ready. -/
theorem hilbert_to_physical_unbounded_operator_bridge_ready :
    hilbertToPhysicalUnboundedOperatorBridgeData.ready := by
  exact And.intro hilbertToPhysicalUnboundedOperatorBridgeData.hilbertLaneReady <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.hilbertInstanceHardened <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.exactValuePreserved <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.physicalOperatorReady <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.domainPreserved <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.symmetricOnDomain <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.selfAdjointCertificate <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.rayleighLowerBound <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.distinguishedAttainsExact <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.bridgeEstablished_proof <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.concreteYangMillsHamiltonianStillOpen <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.spectralRealizationStillOpen <|
    And.intro hilbertToPhysicalUnboundedOperatorBridgeData.publicBoundaryHeld
      hilbertToPhysicalUnboundedOperatorBridgeData.finalReleaseHeld

end MathlibAnalytic
end MGAP4D
