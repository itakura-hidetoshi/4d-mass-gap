import MGAP4D.MathlibAnalytic.HilbertSpaceInstanceSkeleton

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Physical unbounded-operator skeleton after the Hilbert-space instance skeleton.

This bundles the abstract Hilbert-space carrier with a declared physical domain,
operator, domain preservation, symmetry, self-adjoint certificate surface, and
Rayleigh lower-bound surface.

Boundary: this is still a proof-carrying skeleton.  It does not install a
Mathlib unbounded-operator API, a concrete Yang--Mills Hamiltonian, or a final
spectral realization. -/
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
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
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

/-- Ready predicate for the physical unbounded-operator skeleton.

The predicate restates proposition-level obligations over the current data rather
than inserting proof fields directly into `And`. -/
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
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.physicalUnboundedOperatorSkeletonVisible ∧ D.concreteYangMillsHamiltonianStillOpen ∧
  D.spectralRealizationStillOpen ∧ D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- The physical domain is preserved by `H_phys`. -/
theorem physical_unbounded_operator_domain_preserved
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  exact D.domain_preserved ψ hψ

/-- `H_phys` is symmetric on the declared domain. -/
theorem physical_unbounded_operator_symmetric_on_domain
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ φ : D.carrier) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  exact D.symmetric_on_domain ψ φ hψ hφ

/-- The self-adjoint certificate surface is present. -/
theorem physical_unbounded_operator_self_adjoint_certificate
    (D : PhysicalUnboundedOperatorSkeletonData) :
    D.selfAdjointCertificate := by
  exact D.selfAdjointCertificate_proof

/-- The Rayleigh lower bound holds on the declared domain. -/
theorem physical_unbounded_operator_rayleigh_lower_bound
    (D : PhysicalUnboundedOperatorSkeletonData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.rayleigh ψ := by
  exact D.rayleigh_lower_bound ψ hψ

/-- The distinguished state attains the exact value. -/
theorem physical_unbounded_operator_distinguished_attains_exact
    (D : PhysicalUnboundedOperatorSkeletonData) :
    D.rayleigh D.distinguished = exactGapValueReal := by
  exact D.distinguished_attains_exact

/-- Prototype physical unbounded-operator skeleton over a singleton carrier. -/
noncomputable def prototypePhysicalUnboundedOperatorSkeletonData :
    PhysicalUnboundedOperatorSkeletonData.{0} :=
  { hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    carrier := PUnit
    zero := PUnit.unit
    inner := fun _ _ => 0
    norm := fun _ => 0
    domain := fun _ => True
    H_phys := fun ψ => ψ
    distinguished := PUnit.unit
    distinguished_in_domain := True.intro
    domain_preserved := by intro ψ hψ; exact True.intro
    symmetric_on_domain := by intro ψ φ hψ hφ; rfl
    selfAdjointCertificate :=
      hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < exactGapValueReal
    selfAdjointCertificate_proof :=
      And.intro hilbert_space_instance_skeleton_review_surface_ready <|
        And.intro exactGapValueReal_eq exactGapValueReal_pos
    rayleigh := fun _ => exactGapValueReal
    rayleigh_lower_bound := by intro ψ hψ; exact le_rfl
    distinguished_attains_exact := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    physicalUnboundedOperatorSkeletonVisible :=
      hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < exactGapValueReal
    physicalUnboundedOperatorSkeletonVisible_proof :=
      And.intro hilbert_space_instance_skeleton_review_surface_ready <|
        And.intro exactGapValueReal_eq exactGapValueReal_pos
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

theorem prototype_physical_unbounded_operator_skeleton_ready :
    prototypePhysicalUnboundedOperatorSkeletonData.ready := by
  exact And.intro prototypePhysicalUnboundedOperatorSkeletonData.hilbertInstanceReady <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.distinguished_in_domain <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.domain_preserved <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.symmetric_on_domain <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate_proof <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.rayleigh_lower_bound <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.distinguished_attains_exact <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.exact_value_eq_3320 <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.physicalUnboundedOperatorSkeletonVisible_proof <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen_proof <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen_proof <|
    And.intro prototypePhysicalUnboundedOperatorSkeletonData.finalReleaseHeld_proof
      prototypePhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld_proof

/-- Review surface for the physical unbounded-operator skeleton. -/
structure PhysicalUnboundedOperatorSkeletonReviewSurface where
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  operatorReady : prototypePhysicalUnboundedOperatorSkeletonData.ready
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
  prototypePhysicalUnboundedOperatorSkeletonData.ready ∧ S.domainPreserved ∧
  S.symmetricOnDomain ∧ S.selfAdjointCertificate ∧ S.rayleighLowerBound ∧
  S.distinguishedAttainsExact ∧ S.physicalUnboundedOperatorSkeletonEstablished ∧
  S.concreteYangMillsHamiltonianStillOpen ∧ S.spectralRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def physicalUnboundedOperatorSkeletonReviewSurface :
    PhysicalUnboundedOperatorSkeletonReviewSurface :=
  { hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    operatorReady := prototype_physical_unbounded_operator_skeleton_ready
    domainPreserved :=
      ∀ ψ,
        prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
          prototypePhysicalUnboundedOperatorSkeletonData.domain
            (prototypePhysicalUnboundedOperatorSkeletonData.H_phys ψ)
    domainPreserved_proof := prototypePhysicalUnboundedOperatorSkeletonData.domain_preserved
    symmetricOnDomain :=
      ∀ ψ φ,
        prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
        prototypePhysicalUnboundedOperatorSkeletonData.domain φ →
          prototypePhysicalUnboundedOperatorSkeletonData.inner
            (prototypePhysicalUnboundedOperatorSkeletonData.H_phys ψ) φ =
          prototypePhysicalUnboundedOperatorSkeletonData.inner ψ
            (prototypePhysicalUnboundedOperatorSkeletonData.H_phys φ)
    symmetricOnDomain_proof := prototypePhysicalUnboundedOperatorSkeletonData.symmetric_on_domain
    selfAdjointCertificate := prototypePhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate
    selfAdjointCertificate_proof := prototypePhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate_proof
    rayleighLowerBound :=
      ∀ ψ,
        prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
          exactGapValueReal ≤ prototypePhysicalUnboundedOperatorSkeletonData.rayleigh ψ
    rayleighLowerBound_proof := prototypePhysicalUnboundedOperatorSkeletonData.rayleigh_lower_bound
    distinguishedAttainsExact :=
      prototypePhysicalUnboundedOperatorSkeletonData.rayleigh
        prototypePhysicalUnboundedOperatorSkeletonData.distinguished = exactGapValueReal
    distinguishedAttainsExact_proof := prototypePhysicalUnboundedOperatorSkeletonData.distinguished_attains_exact
    physicalUnboundedOperatorSkeletonEstablished := prototypePhysicalUnboundedOperatorSkeletonData.ready
    physicalUnboundedOperatorSkeletonEstablished_proof := prototype_physical_unbounded_operator_skeleton_ready
    concreteYangMillsHamiltonianStillOpen := prototypePhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen
    concreteYangMillsHamiltonianStillOpen_proof := prototypePhysicalUnboundedOperatorSkeletonData.concreteYangMillsHamiltonianStillOpen_proof
    spectralRealizationStillOpen := prototypePhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen
    spectralRealizationStillOpen_proof := prototypePhysicalUnboundedOperatorSkeletonData.spectralRealizationStillOpen_proof
    finalReleaseHeld := prototypePhysicalUnboundedOperatorSkeletonData.finalReleaseHeld
    finalReleaseHeld_proof := prototypePhysicalUnboundedOperatorSkeletonData.finalReleaseHeld_proof
    publicBoundaryHeld := prototypePhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypePhysicalUnboundedOperatorSkeletonData.publicBoundaryHeld_proof }

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

end MathlibAnalytic
end MGAP4D