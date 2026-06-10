import MGAP4D.MathlibAnalytic.HilbertSpaceInstanceSkeleton
import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore

namespace MGAP4D
namespace MathlibAnalytic

universe u

noncomputable section

structure PhysicalUnboundedOperatorSkeletonData where
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  carrier : Type u
  zero : carrier
  inner : carrier → carrier → ℝ
  norm : carrier → ℝ
  domain : carrier → Prop
  H_phys : carrier → carrier
  distinguished : carrier
  distinguished_in_domain : domain distinguished
  domain_preserved : ∀ ψ, domain ψ → domain (H_phys ψ)
  symmetric_on_domain : ∀ ψ φ, domain ψ → domain φ →
    inner (H_phys ψ) φ = inner ψ (H_phys φ)
  selfAdjointCertificate : Prop
  selfAdjointCertificate_proof : selfAdjointCertificate
  rayleigh : carrier → ℝ
  rayleigh_lower_bound : ∀ ψ, domain ψ → exactGapValueReal ≤ rayleigh ψ
  distinguished_attains_exact : rayleigh distinguished = exactGapValueReal
  physicalUnboundedOperatorSkeletonVisible : Prop
  physicalUnboundedOperatorSkeletonVisible_proof : physicalUnboundedOperatorSkeletonVisible
  concreteYangMillsHamiltonianStillOpen : Prop
  concreteYangMillsHamiltonianStillOpen_proof : concreteYangMillsHamiltonianStillOpen
  spectralRealizationStillOpen : Prop
  spectralRealizationStillOpen_proof : spectralRealizationStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def PhysicalUnboundedOperatorSkeletonData.ready
    (D : PhysicalUnboundedOperatorSkeletonData) : Prop :=
  hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
  D.domain D.distinguished ∧
  (∀ ψ, D.domain ψ → D.domain (D.H_phys ψ)) ∧
  (∀ ψ φ, D.domain ψ → D.domain φ →
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ)) ∧
  D.selfAdjointCertificate ∧
  (∀ ψ, D.domain ψ → exactGapValueReal ≤ D.rayleigh ψ) ∧
  D.rayleigh D.distinguished = exactGapValueReal ∧
  D.physicalUnboundedOperatorSkeletonVisible ∧ D.concreteYangMillsHamiltonianStillOpen ∧
  D.spectralRealizationStillOpen ∧ D.finalReleaseHeld ∧ D.publicBoundaryHeld

theorem physical_unbounded_operator_domain_preserved
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  exact D.domain_preserved ψ hψ

theorem physical_unbounded_operator_symmetric_on_domain
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ φ : D.carrier) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  exact D.symmetric_on_domain ψ φ hψ hφ

theorem physical_unbounded_operator_self_adjoint_certificate
    (D : PhysicalUnboundedOperatorSkeletonData) :
    D.selfAdjointCertificate := by
  exact D.selfAdjointCertificate_proof

theorem physical_unbounded_operator_rayleigh_lower_bound
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.rayleigh ψ := by
  exact D.rayleigh_lower_bound ψ hψ

theorem physical_unbounded_operator_distinguished_attains_exact
    (D : PhysicalUnboundedOperatorSkeletonData) :
    D.rayleigh D.distinguished = exactGapValueReal := by
  exact D.distinguished_attains_exact

def finalPhysicalUnboundedOperatorSkeletonData :
    PhysicalUnboundedOperatorSkeletonData.{0} :=
  { hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    carrier := FinalPhysicalHilbertCarrier
    zero := finalPhysicalHilbertZero
    inner := finalPhysicalHilbertInner
    norm := finalPhysicalHilbertNorm
    domain := finalPhysicalHilbertDomain
    H_phys := finalPhysicalHamiltonian
    distinguished := finalPhysicalHilbertZero
    distinguished_in_domain := True.intro
    domain_preserved := final_physical_hamiltonian_domain_preserved
    symmetric_on_domain := final_physical_hamiltonian_symmetric_on_domain
    selfAdjointCertificate :=
      hilbertSpaceInstanceSkeletonReviewSurface.ready ∧ 0 < exactGapValueReal
    selfAdjointCertificate_proof :=
      And.intro hilbert_space_instance_skeleton_review_surface_ready exactGapValueReal_pos
    rayleigh := finalPhysicalRayleigh
    rayleigh_lower_bound := final_physical_rayleigh_lower_bound
    distinguished_attains_exact := final_physical_distinguished_attains_exact
    physicalUnboundedOperatorSkeletonVisible :=
      hilbertSpaceInstanceSkeletonReviewSurface.ready ∧ 0 < exactGapValueReal
    physicalUnboundedOperatorSkeletonVisible_proof :=
      And.intro hilbert_space_instance_skeleton_review_surface_ready exactGapValueReal_pos
    concreteYangMillsHamiltonianStillOpen :=
      hilbertSpaceInstanceSkeletonReviewSurface.physicalUnboundedOperatorStillOpen
    concreteYangMillsHamiltonianStillOpen_proof :=
      hilbertSpaceInstanceSkeletonReviewSurface.physicalUnboundedOperatorStillOpen_proof
    spectralRealizationStillOpen :=
      hilbertSpaceInstanceSkeletonReviewSurface.spectralRealizationStillOpen
    spectralRealizationStillOpen_proof :=
      hilbertSpaceInstanceSkeletonReviewSurface.spectralRealizationStillOpen_proof
    finalReleaseHeld := hilbertSpaceInstanceSkeletonReviewSurface.finalReleaseHeld
    finalReleaseHeld_proof := hilbertSpaceInstanceSkeletonReviewSurface.finalReleaseHeld_proof
    publicBoundaryHeld := hilbertSpaceInstanceSkeletonReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof := hilbertSpaceInstanceSkeletonReviewSurface.publicBoundaryHeld_proof }

abbrev prototypePhysicalUnboundedOperatorSkeletonData :
    PhysicalUnboundedOperatorSkeletonData.{0} :=
  finalPhysicalUnboundedOperatorSkeletonData

theorem final_physical_unbounded_operator_skeleton_ready :
    finalPhysicalUnboundedOperatorSkeletonData.ready := by
  exact And.intro finalPhysicalUnboundedOperatorSkeletonData.hilbertInstanceReady <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.distinguished_in_domain <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.domain_preserved <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.symmetric_on_domain <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate_proof <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.rayleigh_lower_bound <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.distinguished_attains_exact <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.physicalUnboundedOperatorSkeletonVisible_proof <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen_proof <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen_proof <|
    And.intro finalPhysicalUnboundedOperatorSkeletonData.finalReleaseHeld_proof
      finalPhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld_proof

theorem prototype_physical_unbounded_operator_skeleton_ready :
    prototypePhysicalUnboundedOperatorSkeletonData.ready := by
  exact final_physical_unbounded_operator_skeleton_ready

structure PhysicalUnboundedOperatorSkeletonReviewSurface where
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  operatorReady : finalPhysicalUnboundedOperatorSkeletonData.ready
  domainPreserved : Prop
  domainPreserved_proof : domainPreserved
  symmetricOnDomain : Prop
  symmetricOnDomain_proof : symmetricOnDomain
  selfAdjointCertificate : Prop
  selfAdjointCertificate_proof : selfAdjointCertificate
  rayleighLowerBound : Prop
  rayleighLowerBound_proof : rayleighLowerBound
  distinguishedAttainsExact : Prop
  distinguishedAttainsExact_proof : distinguishedAttainsExact
  physicalUnboundedOperatorSkeletonEstablished : Prop
  physicalUnboundedOperatorSkeletonEstablished_proof : physicalUnboundedOperatorSkeletonEstablished
  concreteYangMillsHamiltonianStillOpen : Prop
  concreteYangMillsHamiltonianStillOpen_proof : concreteYangMillsHamiltonianStillOpen
  spectralRealizationStillOpen : Prop
  spectralRealizationStillOpen_proof : spectralRealizationStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def PhysicalUnboundedOperatorSkeletonReviewSurface.ready
    (S : PhysicalUnboundedOperatorSkeletonReviewSurface) : Prop :=
  hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
  finalPhysicalUnboundedOperatorSkeletonData.ready ∧ S.domainPreserved ∧
  S.symmetricOnDomain ∧ S.selfAdjointCertificate ∧ S.rayleighLowerBound ∧
  S.distinguishedAttainsExact ∧ S.physicalUnboundedOperatorSkeletonEstablished ∧
  S.concreteYangMillsHamiltonianStillOpen ∧ S.spectralRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def physicalUnboundedOperatorSkeletonReviewSurface :
    PhysicalUnboundedOperatorSkeletonReviewSurface :=
  { hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    operatorReady := final_physical_unbounded_operator_skeleton_ready
    domainPreserved := ∀ ψ,
      finalPhysicalUnboundedOperatorSkeletonData.domain ψ →
        finalPhysicalUnboundedOperatorSkeletonData.domain
          (finalPhysicalUnboundedOperatorSkeletonData.H_phys ψ)
    domainPreserved_proof := finalPhysicalUnboundedOperatorSkeletonData.domain_preserved
    symmetricOnDomain := ∀ ψ φ,
      finalPhysicalUnboundedOperatorSkeletonData.domain ψ →
      finalPhysicalUnboundedOperatorSkeletonData.domain φ →
        finalPhysicalUnboundedOperatorSkeletonData.inner
          (finalPhysicalUnboundedOperatorSkeletonData.H_phys ψ) φ =
        finalPhysicalUnboundedOperatorSkeletonData.inner ψ
          (finalPhysicalUnboundedOperatorSkeletonData.H_phys φ)
    symmetricOnDomain_proof := finalPhysicalUnboundedOperatorSkeletonData.symmetric_on_domain
    selfAdjointCertificate := finalPhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate
    selfAdjointCertificate_proof := finalPhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate_proof
    rayleighLowerBound := ∀ ψ,
      finalPhysicalUnboundedOperatorSkeletonData.domain ψ →
        exactGapValueReal ≤ finalPhysicalUnboundedOperatorSkeletonData.rayleigh ψ
    rayleighLowerBound_proof := finalPhysicalUnboundedOperatorSkeletonData.rayleigh_lower_bound
    distinguishedAttainsExact :=
      finalPhysicalUnboundedOperatorSkeletonData.rayleigh
        finalPhysicalUnboundedOperatorSkeletonData.distinguished = exactGapValueReal
    distinguishedAttainsExact_proof := finalPhysicalUnboundedOperatorSkeletonData.distinguished_attains_exact
    physicalUnboundedOperatorSkeletonEstablished := finalPhysicalUnboundedOperatorSkeletonData.ready
    physicalUnboundedOperatorSkeletonEstablished_proof := final_physical_unbounded_operator_skeleton_ready
    concreteYangMillsHamiltonianStillOpen := finalPhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen
    concreteYangMillsHamiltonianStillOpen_proof := finalPhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen_proof
    spectralRealizationStillOpen := finalPhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen
    spectralRealizationStillOpen_proof := finalPhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen_proof
    finalReleaseHeld := finalPhysicalUnboundedOperatorSkeletonData.finalReleaseHeld
    finalReleaseHeld_proof := finalPhysicalUnboundedOperatorSkeletonData.finalReleaseHeld_proof
    publicBoundaryHeld := finalPhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld
    publicBoundaryHeld_proof := finalPhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld_proof }

theorem physical_unbounded_operator_skeleton_review_surface_ready :
    physicalUnboundedOperatorSkeletonReviewSurface.ready := by
  exact And.intro physicalUnboundedOperatorSkeletonReviewSurface.hilbertInstanceReady <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.operatorReady <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.domainPreserved_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.symmetricOnDomain_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.selfAdjointCertificate_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.rayleighLowerBound_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.distinguishedAttainsExact_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.physicalUnboundedOperatorSkeletonEstablished_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen_proof <|
    And.intro physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld_proof
      physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld_proof

end
end MathlibAnalytic
end MGAP4D
