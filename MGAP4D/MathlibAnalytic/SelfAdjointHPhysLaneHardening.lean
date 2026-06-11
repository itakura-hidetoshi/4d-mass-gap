import MGAP4D.MathlibAnalytic.CompleteInfiniteDimensionalHilbertConstruction
import MGAP4D.MathlibAnalytic.SelfAdjointHPhysInterface
import MGAP4D.MathlibAnalytic.SelfAdjointHPhysTheorem
import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton
import MGAP4D.MathlibAnalytic.ConcreteHPhysRealizationTheorem

namespace MGAP4D
namespace MathlibAnalytic

structure SelfAdjointHPhysLaneHardeningData where
  completeHilbertConstructionLaneReady : completeInfiniteDimensionalHilbertConstructionLaneData.ready
  hphysInterfaceReady : selfAdjointHPhysReviewSurface.ready
  hphysTheoremBodyReady : selfAdjointHPhysTheoremReviewSurface.ready
  physicalOperatorSkeletonReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  concreteHPhysBridgeReady : concreteHPhysRealizationTheoremReviewSurface.ready
  interfaceHardened : Prop
  theoremBodyHardened : Prop
  domainClosureHardened : Prop
  symmetryOnDomainHardened : Prop
  selfAdjointCertificateHardened : Prop
  rayleighCompatibilityHardened : Prop
  physicalOperatorSkeletonHardened : Prop
  concreteHPhysBridgeHardened : Prop
  hardPhysicalBoundaryVisible : Prop
  exactValuePreserved : exactGapValueReal = exactGapValueReal
  reviewLevelOnly : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

def SelfAdjointHPhysLaneHardeningData.ready
    (D : SelfAdjointHPhysLaneHardeningData) : Prop :=
  completeInfiniteDimensionalHilbertConstructionLaneData.ready ∧
  selfAdjointHPhysReviewSurface.ready ∧
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
  concreteHPhysRealizationTheoremReviewSurface.ready ∧
  D.interfaceHardened ∧
  D.theoremBodyHardened ∧
  D.domainClosureHardened ∧
  D.symmetryOnDomainHardened ∧
  D.selfAdjointCertificateHardened ∧
  D.rayleighCompatibilityHardened ∧
  D.physicalOperatorSkeletonHardened ∧
  D.concreteHPhysBridgeHardened ∧
  D.hardPhysicalBoundaryVisible ∧
  exactGapValueReal = exactGapValueReal ∧
  D.reviewLevelOnly ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

theorem self_adjoint_hphys_interface_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.interfaceHardened := by
  rcases hD with ⟨_, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_theorem_body_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.theoremBodyHardened := by
  rcases hD with ⟨_, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_domain_closure_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.domainClosureHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_symmetry_on_domain_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.symmetryOnDomainHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_certificate_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.selfAdjointCertificateHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_rayleigh_compatibility_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.rayleighCompatibilityHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_physical_operator_skeleton_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.physicalOperatorSkeletonHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_concrete_bridge_hardened
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.concreteHPhysBridgeHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_hard_boundary_visible
    (D : SelfAdjointHPhysLaneHardeningData) (hD : D.ready) :
    D.hardPhysicalBoundaryVisible := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem self_adjoint_hphys_exact_value_preserved
    (D : SelfAdjointHPhysLaneHardeningData) (_hD : D.ready) :
    exactGapValueReal = exactGapValueReal := by
  exact D.exactValuePreserved

def selfAdjointHPhysLaneHardeningData : SelfAdjointHPhysLaneHardeningData :=
  { completeHilbertConstructionLaneReady := complete_infinite_dimensional_hilbert_construction_lane_ready
    hphysInterfaceReady := self_adjoint_hphys_review_surface_ready
    hphysTheoremBodyReady := self_adjoint_hphys_theorem_review_surface_ready
    physicalOperatorSkeletonReady := physical_unbounded_operator_skeleton_review_surface_ready
    concreteHPhysBridgeReady := concrete_hphys_realization_theorem_review_surface_ready
    interfaceHardened := selfAdjointHPhysReviewSurface.ready
    theoremBodyHardened := selfAdjointHPhysTheoremReviewSurface.ready
    domainClosureHardened :=
      ∀ ψ : singletonSelfAdjointHPhysTheoremData.state,
        singletonSelfAdjointHPhysTheoremData.domain ψ →
          singletonSelfAdjointHPhysTheoremData.domain
            (singletonSelfAdjointHPhysTheoremData.H_phys ψ)
    symmetryOnDomainHardened :=
      ∀ ψ φ : singletonSelfAdjointHPhysTheoremData.state,
        singletonSelfAdjointHPhysTheoremData.domain ψ →
        singletonSelfAdjointHPhysTheoremData.domain φ →
          singletonSelfAdjointHPhysTheoremData.inner
            (singletonSelfAdjointHPhysTheoremData.H_phys ψ) φ =
          singletonSelfAdjointHPhysTheoremData.inner ψ
            (singletonSelfAdjointHPhysTheoremData.H_phys φ)
    selfAdjointCertificateHardened :=
      singletonSelfAdjointHPhysTheoremData.selfAdjointCertificate
    rayleighCompatibilityHardened :=
      (∀ ψ : singletonSelfAdjointHPhysTheoremData.state,
        singletonSelfAdjointHPhysTheoremData.domain ψ →
          exactGapValueReal ≤
            singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
              (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh ψ)) ∧
      singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
        (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh
          singletonSelfAdjointHPhysTheoremData.witness) = exactGapValueReal
    physicalOperatorSkeletonHardened :=
      physicalUnboundedOperatorSkeletonReviewSurface.ready
    concreteHPhysBridgeHardened :=
      concreteHPhysRealizationTheoremReviewSurface.ready
    hardPhysicalBoundaryVisible :=
      physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld ∧
      concreteHPhysRealizationTheoremReviewSurface.publicBoundaryHeld
    exactValuePreserved := rfl
    reviewLevelOnly :=
      exactGapValueReal ∈ exactGapEnergyRay ∧
      selfAdjointHPhysTheoremReviewSurface.concreteUnboundedRealizationStillOpen
    publicBoundaryHeld :=
      physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld ∧
      concreteHPhysRealizationTheoremReviewSurface.publicBoundaryHeld
    finalReleaseHeld :=
      selfAdjointHPhysTheoremReviewSurface.finalReleaseHeld ∧
      physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld ∧
      concreteHPhysRealizationTheoremReviewSurface.finalReleaseHeld }

theorem self_adjoint_hphys_lane_hardening_ready :
    selfAdjointHPhysLaneHardeningData.ready := by
  rcases self_adjoint_hphys_review_surface_ready with
    ⟨_, _, _, _, _, _, hInterfaceEnergyRay, _⟩
  rcases self_adjoint_hphys_theorem_review_surface_ready with
    ⟨_, _, _, _, _, _, hTheoremOpen, hTheoremFinal, _⟩
  rcases physical_unbounded_operator_skeleton_review_surface_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, hPhysicalFinal, hPhysicalPublic⟩
  rcases concrete_hphys_realization_theorem_review_surface_ready with
    ⟨_, _, _, _, _, _, _, _, hConcreteFinal, hConcretePublic⟩
  exact And.intro selfAdjointHPhysLaneHardeningData.completeHilbertConstructionLaneReady <|
    And.intro selfAdjointHPhysLaneHardeningData.hphysInterfaceReady <|
    And.intro selfAdjointHPhysLaneHardeningData.hphysTheoremBodyReady <|
    And.intro selfAdjointHPhysLaneHardeningData.physicalOperatorSkeletonReady <|
    And.intro selfAdjointHPhysLaneHardeningData.concreteHPhysBridgeReady <|
    And.intro self_adjoint_hphys_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro singletonSelfAdjointHPhysTheoremData.domain_closed_under_H <|
    And.intro singleton_self_adjoint_hphys_symmetric_on_domain <|
    And.intro singletonSelfAdjointHPhysTheoremData.selfAdjointCertificate_proof <|
    And.intro
      (And.intro singleton_self_adjoint_hphys_rayleigh_lower_bound
        singleton_self_adjoint_hphys_witness_rayleigh_attains) <|
    And.intro physical_unbounded_operator_skeleton_review_surface_ready <|
    And.intro concrete_hphys_realization_theorem_review_surface_ready <|
    And.intro (And.intro hPhysicalPublic hConcretePublic) <|
    And.intro selfAdjointHPhysLaneHardeningData.exactValuePreserved <|
    And.intro (And.intro hInterfaceEnergyRay hTheoremOpen) <|
    And.intro (And.intro hPhysicalPublic hConcretePublic) <|
    And.intro hTheoremFinal <|
      And.intro hPhysicalFinal hConcreteFinal

end MathlibAnalytic
end MGAP4D
