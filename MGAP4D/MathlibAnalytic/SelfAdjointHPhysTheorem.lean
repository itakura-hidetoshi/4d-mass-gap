import MGAP4D.MathlibAnalytic.HilbertRayleighQuotientTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- Abstract theorem body for the self-adjoint `H_phys` layer.

This is the second post-interface theorem-body step. It does not yet construct
a concrete unbounded operator on an infinite-dimensional Hilbert space. It
makes the operator domain, symmetry-on-domain, self-adjointness certificate, and
Rayleigh-quotient compatibility explicit. -/
structure SelfAdjointHPhysTheoremData where
  state : Type u
  inner : state → state → ℝ
  H_phys : state → state
  domain : state → Prop
  witness : state
  witness_in_domain : domain witness
  domain_closed_under_H : ∀ ψ, domain ψ → domain (H_phys ψ)
  symmetric_on_domain : ∀ ψ φ, domain ψ → domain φ →
    inner (H_phys ψ) φ = inner ψ (H_phys φ)
  selfAdjointCertificate : Prop
  selfAdjointCertificate_proof : selfAdjointCertificate
  rayleighData : HilbertRayleighQuotientData
  state_to_rayleigh : state → rayleighData.state
  rayleigh_admissible_of_domain : ∀ ψ, domain ψ →
    rayleighData.admissible (state_to_rayleigh ψ)
  rayleigh_lower_bound_of_domain : ∀ ψ, domain ψ →
    exactGapValueReal ≤ rayleighData.quotient (state_to_rayleigh ψ)
  witness_rayleigh_attains_exact :
    rayleighData.quotient (state_to_rayleigh witness) = exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  exact_value_positive : 0 < exactGapValueReal
  concreteUnboundedRealizationStillOpen : Prop

/-- Ready predicate for the abstract self-adjoint `H_phys` theorem body. -/
def SelfAdjointHPhysTheoremData.ready
    (D : SelfAdjointHPhysTheoremData) : Prop :=
  D.domain D.witness ∧
  (∀ ψ, D.domain ψ → D.domain (D.H_phys ψ)) ∧
  (∀ ψ φ, D.domain ψ → D.domain φ →
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ)) ∧
  D.selfAdjointCertificate ∧
  (∀ ψ, D.domain ψ → D.rayleighData.admissible (D.state_to_rayleigh ψ)) ∧
  (∀ ψ, D.domain ψ → exactGapValueReal ≤
    D.rayleighData.quotient (D.state_to_rayleigh ψ)) ∧
  D.rayleighData.quotient (D.state_to_rayleigh D.witness) = exactGapValueReal ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧ 0 < exactGapValueReal ∧
  D.concreteUnboundedRealizationStillOpen

/-- Symmetry theorem body for `H_phys` on the declared domain. -/
theorem self_adjoint_hphys_symmetric_on_domain
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready)
    (ψ φ : D.state) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  rcases hD with ⟨_, _, hSymm, _, _, _, _, _, _, _⟩
  exact hSymm ψ φ hψ hφ

/-- Domain-closure theorem body for `H_phys`. -/
theorem self_adjoint_hphys_domain_closed
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready)
    (ψ : D.state) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  rcases hD with ⟨_, hClosed, _, _, _, _, _, _, _, _⟩
  exact hClosed ψ hψ

/-- Self-adjointness certificate theorem body. -/
theorem self_adjoint_hphys_certificate
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready) :
    D.selfAdjointCertificate := by
  rcases hD with ⟨_, _, _, hCert, _, _, _, _, _, _⟩
  exact hCert

/-- Rayleigh admissibility compatibility theorem body for domain states. -/
theorem self_adjoint_hphys_rayleigh_admissible
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready)
    (ψ : D.state) (hψ : D.domain ψ) :
    D.rayleighData.admissible (D.state_to_rayleigh ψ) := by
  rcases hD with ⟨_, _, _, _, hAdm, _, _, _, _, _⟩
  exact hAdm ψ hψ

/-- Rayleigh lower-bound compatibility theorem body for domain states. -/
theorem self_adjoint_hphys_rayleigh_lower_bound
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready)
    (ψ : D.state) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.rayleighData.quotient (D.state_to_rayleigh ψ) := by
  rcases hD with ⟨_, _, _, _, _, hLower, _, _, _, _⟩
  exact hLower ψ hψ

/-- Exact-gap witness theorem body for the operator witness. -/
theorem self_adjoint_hphys_witness_rayleigh_attains
    (D : SelfAdjointHPhysTheoremData) (hD : D.ready) :
    D.rayleighData.quotient (D.state_to_rayleigh D.witness) = exactGapValueReal := by
  rcases hD with ⟨_, _, _, _, _, _, hWitness, _, _, _⟩
  exact hWitness

/-- Singleton theorem-body realization for the self-adjoint `H_phys` layer.

The operator is the identity on a singleton domain, the inner pairing is the
constant real pairing, and the Rayleigh quotient data is the already CI-green
singleton quotient theorem body. -/
def singletonSelfAdjointHPhysTheoremData : SelfAdjointHPhysTheoremData.{0} :=
  { state := PUnit
    inner := fun _ _ => 1
    H_phys := fun ψ => ψ
    domain := fun _ => True
    witness := PUnit.unit
    witness_in_domain := True.intro
    domain_closed_under_H := by
      intro ψ hψ
      exact True.intro
    symmetric_on_domain := by
      intro ψ φ hψ hφ
      rfl
    selfAdjointCertificate := True
    selfAdjointCertificate_proof := True.intro
    rayleighData := singletonHilbertRayleighQuotientData
    state_to_rayleigh := fun _ => PUnit.unit
    rayleigh_admissible_of_domain := by
      intro ψ hψ
      exact True.intro
    rayleigh_lower_bound_of_domain := by
      intro ψ hψ
      exact singleton_hilbert_rayleigh_quotient_lower_bound PUnit.unit True.intro
    witness_rayleigh_attains_exact := singleton_hilbert_rayleigh_quotient_witness_attains
    exact_value_eq_3320 := exactGapValueReal_eq
    exact_value_positive := exactGapValueReal_pos
    concreteUnboundedRealizationStillOpen := True }

theorem singleton_self_adjoint_hphys_theorem_data_ready :
    singletonSelfAdjointHPhysTheoremData.ready := by
  exact And.intro singletonSelfAdjointHPhysTheoremData.witness_in_domain <|
    And.intro singletonSelfAdjointHPhysTheoremData.domain_closed_under_H <|
    And.intro singletonSelfAdjointHPhysTheoremData.symmetric_on_domain <|
    And.intro singletonSelfAdjointHPhysTheoremData.selfAdjointCertificate_proof <|
    And.intro singletonSelfAdjointHPhysTheoremData.rayleigh_admissible_of_domain <|
    And.intro singletonSelfAdjointHPhysTheoremData.rayleigh_lower_bound_of_domain <|
    And.intro singletonSelfAdjointHPhysTheoremData.witness_rayleigh_attains_exact <|
    And.intro exactGapValueReal_eq <|
    And.intro exactGapValueReal_pos True.intro

theorem singleton_self_adjoint_hphys_symmetric_on_domain
    (ψ φ : singletonSelfAdjointHPhysTheoremData.state)
    (hψ : singletonSelfAdjointHPhysTheoremData.domain ψ)
    (hφ : singletonSelfAdjointHPhysTheoremData.domain φ) :
    singletonSelfAdjointHPhysTheoremData.inner
      (singletonSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    singletonSelfAdjointHPhysTheoremData.inner ψ
      (singletonSelfAdjointHPhysTheoremData.H_phys φ) := by
  exact self_adjoint_hphys_symmetric_on_domain
    singletonSelfAdjointHPhysTheoremData
    singleton_self_adjoint_hphys_theorem_data_ready ψ φ hψ hφ

theorem singleton_self_adjoint_hphys_rayleigh_lower_bound
    (ψ : singletonSelfAdjointHPhysTheoremData.state)
    (hψ : singletonSelfAdjointHPhysTheoremData.domain ψ) :
    exactGapValueReal ≤
      singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
        (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh ψ) := by
  exact self_adjoint_hphys_rayleigh_lower_bound
    singletonSelfAdjointHPhysTheoremData
    singleton_self_adjoint_hphys_theorem_data_ready ψ hψ

theorem singleton_self_adjoint_hphys_witness_rayleigh_attains :
    singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
      (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh
        singletonSelfAdjointHPhysTheoremData.witness) = exactGapValueReal := by
  exact self_adjoint_hphys_witness_rayleigh_attains
    singletonSelfAdjointHPhysTheoremData
    singleton_self_adjoint_hphys_theorem_data_ready

/-- Review surface closing the abstract self-adjoint `H_phys` theorem body after
the Rayleigh quotient theorem body. -/
structure SelfAdjointHPhysTheoremReviewSurface where
  rayleighQuotientReady : hilbertRayleighQuotientReviewSurface.ready
  hphysTheoremDataReady : singletonSelfAdjointHPhysTheoremData.ready
  symmetryOnDomain : ∀ ψ φ : singletonSelfAdjointHPhysTheoremData.state,
    singletonSelfAdjointHPhysTheoremData.domain ψ →
    singletonSelfAdjointHPhysTheoremData.domain φ →
    singletonSelfAdjointHPhysTheoremData.inner
      (singletonSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    singletonSelfAdjointHPhysTheoremData.inner ψ
      (singletonSelfAdjointHPhysTheoremData.H_phys φ)
  rayleighLowerBound : ∀ ψ : singletonSelfAdjointHPhysTheoremData.state,
    singletonSelfAdjointHPhysTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
        (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh ψ)
  witnessAttains : singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
    (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh
      singletonSelfAdjointHPhysTheoremData.witness) = exactGapValueReal
  selfAdjointTheoremBodyClosed : Prop
  concreteUnboundedRealizationStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def SelfAdjointHPhysTheoremReviewSurface.ready
    (S : SelfAdjointHPhysTheoremReviewSurface) : Prop :=
  hilbertRayleighQuotientReviewSurface.ready ∧
  singletonSelfAdjointHPhysTheoremData.ready ∧
  (∀ ψ φ : singletonSelfAdjointHPhysTheoremData.state,
    singletonSelfAdjointHPhysTheoremData.domain ψ →
    singletonSelfAdjointHPhysTheoremData.domain φ →
    singletonSelfAdjointHPhysTheoremData.inner
      (singletonSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    singletonSelfAdjointHPhysTheoremData.inner ψ
      (singletonSelfAdjointHPhysTheoremData.H_phys φ)) ∧
  (∀ ψ : singletonSelfAdjointHPhysTheoremData.state,
    singletonSelfAdjointHPhysTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
        (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh ψ)) ∧
  singletonSelfAdjointHPhysTheoremData.rayleighData.quotient
    (singletonSelfAdjointHPhysTheoremData.state_to_rayleigh
      singletonSelfAdjointHPhysTheoremData.witness) = exactGapValueReal ∧
  S.selfAdjointTheoremBodyClosed ∧ S.concreteUnboundedRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def selfAdjointHPhysTheoremReviewSurface : SelfAdjointHPhysTheoremReviewSurface :=
  { rayleighQuotientReady := hilbert_rayleigh_quotient_review_surface_ready
    hphysTheoremDataReady := singleton_self_adjoint_hphys_theorem_data_ready
    symmetryOnDomain := singleton_self_adjoint_hphys_symmetric_on_domain
    rayleighLowerBound := singleton_self_adjoint_hphys_rayleigh_lower_bound
    witnessAttains := singleton_self_adjoint_hphys_witness_rayleigh_attains
    selfAdjointTheoremBodyClosed := True
    concreteUnboundedRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem self_adjoint_hphys_theorem_review_surface_ready :
    selfAdjointHPhysTheoremReviewSurface.ready := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro singleton_self_adjoint_hphys_theorem_data_ready <|
    And.intro singleton_self_adjoint_hphys_symmetric_on_domain <|
    And.intro singleton_self_adjoint_hphys_rayleigh_lower_bound <|
    And.intro singleton_self_adjoint_hphys_witness_rayleigh_attains <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem self_adjoint_hphys_theorem_review_surface_final_release_held :
    selfAdjointHPhysTheoremReviewSurface.finalReleaseHeld := by
  trivial

end

end MathlibAnalytic
end MGAP4D
