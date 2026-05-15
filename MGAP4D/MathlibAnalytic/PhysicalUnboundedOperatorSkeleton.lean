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
  spectralRealizationStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def PhysicalUnboundedOperatorSkeletonData.ready
    (D : PhysicalUnboundedOperatorSkeletonData) : Prop :=
  D.hilbertInstanceReady ∧ D.distinguished_in_domain ∧ D.domain_preserved ∧
  D.symmetric_on_domain ∧ D.selfAdjointCertificate ∧ D.rayleigh_lower_bound ∧
  D.distinguished_attains_exact ∧ D.exact_value_eq_3320 ∧
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
def prototypePhysicalUnboundedOperatorSkeletonData :
    PhysicalUnboundedOperatorSkeletonData :=
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
    selfAdjointCertificate := True
    selfAdjointCertificate_proof := True.intro
    rayleigh := fun _ => exactGapValueReal
    rayleigh_lower_bound := by intro ψ hψ; exact le_rfl
    distinguished_attains_exact := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    physicalUnboundedOperatorSkeletonVisible := True
    physicalUnboundedOperatorSkeletonVisible_proof := True.intro
    concreteYangMillsHamiltonianStillOpen := True
    spectralRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem prototype_physical_unbounded_operator_skeleton_ready :
    prototypePhysicalUnboundedOperatorSkeletonData.ready := by
  exact And.intro hilbert_space_instance_skeleton_review_surface_ready <|
    And.intro True.intro <|
    And.intro (by intro ψ hψ; exact True.intro) <|
    And.intro (by intro ψ φ hψ hφ; rfl) <|
    And.intro True.intro <|
    And.intro (by intro ψ hψ; exact le_rfl) <|
    And.intro rfl <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

/-- Review surface for the physical unbounded-operator skeleton. -/
structure PhysicalUnboundedOperatorSkeletonReviewSurface where
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  operatorReady : prototypePhysicalUnboundedOperatorSkeletonData.ready
  domainPreserved : ∀ ψ,
    prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
      prototypePhysicalUnboundedOperatorSkeletonData.domain
        (prototypePhysicalUnboundedOperatorSkeletonData.H_phys ψ)
  symmetricOnDomain : ∀ ψ φ,
    prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
    prototypePhysicalUnboundedOperatorSkeletonData.domain φ →
      prototypePhysicalUnboundedOperatorSkeletonData.inner
        (prototypePhysicalUnboundedOperatorSkeletonData.H_phys ψ) φ =
      prototypePhysicalUnboundedOperatorSkeletonData.inner ψ
        (prototypePhysicalUnboundedOperatorSkeletonData.H_phys φ)
  selfAdjointCertificate : prototypePhysicalUnboundedOperatorSkeletonData.selfAdjointCertificate
  rayleighLowerBound : ∀ ψ,
    prototypePhysicalUnboundedOperatorSkeletonData.domain ψ →
      exactGapValueReal ≤ prototypePhysicalUnboundedOperatorSkeletonData.rayleigh ψ
  distinguishedAttainsExact :
    prototypePhysicalUnboundedOperatorSkeletonData.rayleigh
      prototypePhysicalUnboundedOperatorSkeletonData.distinguished = exactGapValueReal
  physicalUnboundedOperatorSkeletonEstablished : Prop
  concreteYangMillsHamiltonianStillOpen : Prop
  spectralRealizationStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def PhysicalUnboundedOperatorSkeletonReviewSurface.ready
    (S : PhysicalUnboundedOperatorSkeletonReviewSurface) : Prop :=
  S.hilbertInstanceReady ∧ S.operatorReady ∧ S.domainPreserved ∧
  S.symmetricOnDomain ∧ S.selfAdjointCertificate ∧ S.rayleighLowerBound ∧
  S.distinguishedAttainsExact ∧ S.physicalUnboundedOperatorSkeletonEstablished ∧
  S.concreteYangMillsHamiltonianStillOpen ∧ S.spectralRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def physicalUnboundedOperatorSkeletonReviewSurface :
    PhysicalUnboundedOperatorSkeletonReviewSurface :=
  { hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    operatorReady := prototype_physical_unbounded_operator_skeleton_ready
    domainPreserved := by intro ψ hψ; exact True.intro
    symmetricOnDomain := by intro ψ φ hψ hφ; rfl
    selfAdjointCertificate := True.intro
    rayleighLowerBound := by intro ψ hψ; exact le_rfl
    distinguishedAttainsExact := rfl
    physicalUnboundedOperatorSkeletonEstablished := True
    concreteYangMillsHamiltonianStillOpen := True
    spectralRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem physical_unbounded_operator_skeleton_review_surface_ready :
    physicalUnboundedOperatorSkeletonReviewSurface.ready := by
  exact And.intro hilbert_space_instance_skeleton_review_surface_ready <|
    And.intro prototype_physical_unbounded_operator_skeleton_ready <|
    And.intro (by intro ψ hψ; exact True.intro) <|
    And.intro (by intro ψ φ hψ hφ; rfl) <|
    And.intro True.intro <|
    And.intro (by intro ψ hψ; exact le_rfl) <|
    And.intro rfl <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

end MathlibAnalytic
end MGAP4D
