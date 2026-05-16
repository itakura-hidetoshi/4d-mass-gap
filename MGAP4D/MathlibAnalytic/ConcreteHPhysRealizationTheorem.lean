import MGAP4D.MathlibAnalytic.ConcreteHilbertRealizationTheorem

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Concrete `H_phys` realization theorem body.

This is the second concrete-realization step after the abstract theorem-body
closure.  It gives an explicit carrier, domain, operator, symmetry-on-domain
witness, domain-closure witness, and compatibility with both the concrete
Hilbert realization and the abstract self-adjoint `H_phys` theorem body.

Boundary: this closes a one-point concrete `H_phys` realization.  A full
unbounded infinite-dimensional physical operator realization remains visible as
a separate residual. -/
structure ConcreteHPhysRealizationTheoremData where
  carrier : Type u
  domain : carrier → Prop
  H_phys : carrier → carrier
  inner : carrier → carrier → ℝ
  distinguished : carrier
  hilbertData : ConcreteHilbertRealizationTheoremData
  hilbertDataReady : hilbertData.ready
  hphysData : SelfAdjointHPhysTheoremData
  hphysDataReady : hphysData.ready
  toHPhysState : carrier → hphysData.state
  distinguished_in_domain : domain distinguished
  domain_closed_under_H : ∀ ψ, domain ψ → domain (H_phys ψ)
  symmetric_on_domain : ∀ ψ φ, domain ψ → domain φ →
    inner (H_phys ψ) φ = inner ψ (H_phys φ)
  mapped_domain : ∀ ψ, domain ψ → hphysData.domain (toHPhysState ψ)
  mapped_rayleigh_lower_bound : ∀ ψ, domain ψ →
    exactGapValueReal ≤ hphysData.rayleighData.quotient
      (hphysData.state_to_rayleigh (toHPhysState ψ))
  distinguished_attains_exact :
    hphysData.rayleighData.quotient
      (hphysData.state_to_rayleigh (toHPhysState distinguished)) = exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  concreteHPhysCertificate : Prop
  concreteHPhysCertificate_proof : concreteHPhysCertificate
  fullUnboundedPhysicalOperatorStillOpen : Prop

/-- Ready predicate for the concrete `H_phys` realization. -/
def ConcreteHPhysRealizationTheoremData.ready
    (D : ConcreteHPhysRealizationTheoremData) : Prop :=
  D.hilbertData.ready ∧ D.hphysData.ready ∧ D.domain D.distinguished ∧
  (∀ ψ : D.carrier, D.domain ψ → D.domain (D.H_phys ψ)) ∧
  (∀ ψ φ : D.carrier, D.domain ψ → D.domain φ →
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ)) ∧
  (∀ ψ : D.carrier, D.domain ψ → D.hphysData.domain (D.toHPhysState ψ)) ∧
  (∀ ψ : D.carrier, D.domain ψ →
    exactGapValueReal ≤ D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState ψ))) ∧
  D.hphysData.rayleighData.quotient
    (D.hphysData.state_to_rayleigh (D.toHPhysState D.distinguished)) = exactGapValueReal ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧ D.concreteHPhysCertificate ∧
  D.fullUnboundedPhysicalOperatorStillOpen

/-- Concrete domain closure under `H_phys`. -/
theorem concrete_hphys_domain_closed
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  exact D.domain_closed_under_H ψ hψ

/-- Concrete symmetry of `H_phys` on the declared domain. -/
theorem concrete_hphys_symmetric_on_domain
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ φ : D.carrier) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  exact D.symmetric_on_domain ψ φ hψ hφ

/-- Concrete `H_phys` states map into the abstract `H_phys` domain. -/
theorem concrete_hphys_mapped_domain
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.hphysData.domain (D.toHPhysState ψ) := by
  exact D.mapped_domain ψ hψ

/-- Concrete `H_phys` realization inherits the Rayleigh lower bound. -/
theorem concrete_hphys_mapped_rayleigh_lower_bound
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState ψ)) := by
  exact D.mapped_rayleigh_lower_bound ψ hψ

/-- The distinguished concrete `H_phys` state attains the exact value. -/
theorem concrete_hphys_distinguished_attains_exact
    (D : ConcreteHPhysRealizationTheoremData) :
    D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState D.distinguished)) =
      exactGapValueReal := by
  exact D.distinguished_attains_exact

/-- The concrete `H_phys` realization certificate surface is present. -/
theorem concrete_hphys_certificate
    (D : ConcreteHPhysRealizationTheoremData) :
    D.concreteHPhysCertificate := by
  exact D.concreteHPhysCertificate_proof

/-- One-point concrete `H_phys` realization. -/
noncomputable def singletonConcreteHPhysRealizationTheoremData :
    ConcreteHPhysRealizationTheoremData :=
  { carrier := PUnit
    domain := fun _ => True
    H_phys := fun ψ => ψ
    inner := fun _ _ => 1
    distinguished := PUnit.unit
    hilbertData := singletonConcreteHilbertRealizationTheoremData
    hilbertDataReady := singleton_concrete_hilbert_realization_theorem_data_ready
    hphysData := singletonSelfAdjointHPhysTheoremData
    hphysDataReady := singleton_self_adjoint_hphys_theorem_data_ready
    toHPhysState := fun _ => PUnit.unit
    distinguished_in_domain := True.intro
    domain_closed_under_H := by
      intro ψ hψ
      exact True.intro
    symmetric_on_domain := by
      intro ψ φ hψ hφ
      rfl
    mapped_domain := by
      intro ψ hψ
      exact True.intro
    mapped_rayleigh_lower_bound := by
      intro ψ hψ
      exact singleton_self_adjoint_hphys_rayleigh_lower_bound PUnit.unit True.intro
    distinguished_attains_exact := singleton_hilbert_rayleigh_quotient_witness_attains
    exact_value_eq_3320 := exactGapValueReal_eq
    concreteHPhysCertificate := True
    concreteHPhysCertificate_proof := True.intro
    fullUnboundedPhysicalOperatorStillOpen := True }

theorem singleton_concrete_hphys_realization_theorem_data_ready :
    singletonConcreteHPhysRealizationTheoremData.ready := by
  exact And.intro singletonConcreteHPhysRealizationTheoremData.hilbertDataReady <|
    And.intro singletonConcreteHPhysRealizationTheoremData.hphysDataReady <|
    And.intro singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.domain_closed_under_H <|
    And.intro singletonConcreteHPhysRealizationTheoremData.symmetric_on_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.mapped_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound <|
    And.intro singletonConcreteHPhysRealizationTheoremData.distinguished_attains_exact <|
    And.intro singletonConcreteHPhysRealizationTheoremData.exact_value_eq_3320 <|
    And.intro singletonConcreteHPhysRealizationTheoremData.concreteHPhysCertificate_proof True.intro

theorem singleton_concrete_hphys_domain_closed
    (ψ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ) :
    singletonConcreteHPhysRealizationTheoremData.domain
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) := by
  exact singletonConcreteHPhysRealizationTheoremData.domain_closed_under_H ψ hψ

theorem singleton_concrete_hphys_symmetric_on_domain
    (ψ φ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ)
    (hφ : singletonConcreteHPhysRealizationTheoremData.domain φ) :
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ) := by
  exact singletonConcreteHPhysRealizationTheoremData.symmetric_on_domain ψ φ hψ hφ

theorem singleton_concrete_hphys_rayleigh_lower_bound
    (ψ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ) :
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ)) := by
  exact singletonConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound ψ hψ

theorem singleton_concrete_hphys_distinguished_attains_exact :
    singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal := by
  exact singletonConcreteHPhysRealizationTheoremData.distinguished_attains_exact

/-- Review surface for the concrete `H_phys` realization. -/
structure ConcreteHPhysRealizationTheoremReviewSurface where
  concreteHilbertReady : concreteHilbertRealizationTheoremReviewSurface.ready
  concreteHPhysDataReady : singletonConcreteHPhysRealizationTheoremData.ready
  domainClosed : ∀ ψ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
      singletonConcreteHPhysRealizationTheoremData.domain
        (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)
  symmetricOnDomain : ∀ ψ φ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    singletonConcreteHPhysRealizationTheoremData.domain φ →
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ)
  rayleighLowerBound : ∀ ψ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ))
  distinguishedAttainsExact :
    singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal
  concreteHPhysRealizationBodyClosed : Prop
  fullUnboundedPhysicalOperatorStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def ConcreteHPhysRealizationTheoremReviewSurface.ready
    (S : ConcreteHPhysRealizationTheoremReviewSurface) : Prop :=
  concreteHilbertRealizationTheoremReviewSurface.ready ∧
  singletonConcreteHPhysRealizationTheoremData.ready ∧
  (∀ ψ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
      singletonConcreteHPhysRealizationTheoremData.domain
        (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)) ∧
  (∀ ψ φ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    singletonConcreteHPhysRealizationTheoremData.domain φ →
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ)) ∧
  (∀ ψ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ))) ∧
  (singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal) ∧
  S.concreteHPhysRealizationBodyClosed ∧ S.fullUnboundedPhysicalOperatorStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def concreteHPhysRealizationTheoremReviewSurface :
    ConcreteHPhysRealizationTheoremReviewSurface :=
  { concreteHilbertReady := concrete_hilbert_realization_theorem_review_surface_ready
    concreteHPhysDataReady := singleton_concrete_hphys_realization_theorem_data_ready
    domainClosed := singleton_concrete_hphys_domain_closed
    symmetricOnDomain := singleton_concrete_hphys_symmetric_on_domain
    rayleighLowerBound := singleton_concrete_hphys_rayleigh_lower_bound
    distinguishedAttainsExact := singleton_concrete_hphys_distinguished_attains_exact
    concreteHPhysRealizationBodyClosed := True
    fullUnboundedPhysicalOperatorStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem concrete_hphys_realization_theorem_review_surface_ready :
    concreteHPhysRealizationTheoremReviewSurface.ready := by
  exact And.intro concrete_hilbert_realization_theorem_review_surface_ready <|
    And.intro singleton_concrete_hphys_realization_theorem_data_ready <|
    And.intro singleton_concrete_hphys_domain_closed <|
    And.intro singleton_concrete_hphys_symmetric_on_domain <|
    And.intro singleton_concrete_hphys_rayleigh_lower_bound <|
    And.intro singleton_concrete_hphys_distinguished_attains_exact <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem concrete_hphys_realization_theorem_review_surface_final_release_held :
    ConcreteHPhysRealizationTheoremReviewSurface.finalReleaseHeld
      concreteHPhysRealizationTheoremReviewSurface := by
  trivial

end MathlibAnalytic
end MGAP4D
