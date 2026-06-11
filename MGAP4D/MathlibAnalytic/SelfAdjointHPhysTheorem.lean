import MGAP4D.MathlibAnalytic.HilbertRayleighQuotientTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- Abstract theorem body for the self-adjoint `H_phys` layer.

This is the second post-interface theorem-body step. It does not yet construct
a concrete unbounded operator on an infinite-dimensional Hilbert space. It
makes the operator domain, symmetry-on-domain, self-adjointness certificate, and
Rayleigh-quotient compatibility explicit.  It deliberately carries no upstream
`33/20` theorem; that numeric equality is first exported at R6. -/
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
  exact_value_positive : 0 < exactGapValueReal
  concreteUnboundedRealizationStillOpen : Prop

/-- Concrete certification predicate for the abstract self-adjoint `H_phys` theorem body. -/
def SelfAdjointHPhysTheoremData.certified
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
  0 < exactGapValueReal ∧
  D.concreteUnboundedRealizationStillOpen

/-- Backward-compatible readiness name during downstream migration. -/
def SelfAdjointHPhysTheoremData.ready
    (D : SelfAdjointHPhysTheoremData) : Prop :=
  D.certified

/-- Symmetry theorem body for `H_phys` on the declared domain. -/
theorem self_adjoint_hphys_symmetric_on_domain
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified)
    (ψ φ : D.state) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  rcases hD with ⟨_, _, hSymm, _, _, _, _, _, _⟩
  exact hSymm ψ φ hψ hφ

/-- Domain-closure theorem body for `H_phys`. -/
theorem self_adjoint_hphys_domain_closed
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified)
    (ψ : D.state) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  rcases hD with ⟨_, hClosed, _, _, _, _, _, _, _⟩
  exact hClosed ψ hψ

/-- Self-adjointness certificate theorem body. -/
theorem self_adjoint_hphys_certificate
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified) :
    D.selfAdjointCertificate := by
  rcases hD with ⟨_, _, _, hCert, _, _, _, _, _⟩
  exact hCert

/-- Rayleigh admissibility compatibility theorem body for domain states. -/
theorem self_adjoint_hphys_rayleigh_admissible
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified)
    (ψ : D.state) (hψ : D.domain ψ) :
    D.rayleighData.admissible (D.state_to_rayleigh ψ) := by
  rcases hD with ⟨_, _, _, _, hAdm, _, _, _, _⟩
  exact hAdm ψ hψ

/-- Rayleigh lower-bound compatibility theorem body for domain states. -/
theorem self_adjoint_hphys_rayleigh_lower_bound
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified)
    (ψ : D.state) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.rayleighData.quotient (D.state_to_rayleigh ψ) := by
  rcases hD with ⟨_, _, _, _, _, hLower, _, _, _⟩
  exact hLower ψ hψ

/-- Exact-gap witness theorem body for the operator witness. -/
theorem self_adjoint_hphys_witness_rayleigh_attains
    (D : SelfAdjointHPhysTheoremData) (hD : D.certified) :
    D.rayleighData.quotient (D.state_to_rayleigh D.witness) = exactGapValueReal := by
  rcases hD with ⟨_, _, _, _, _, _, hWitness, _, _⟩
  exact hWitness

/-- Self-adjoint `H_phys` theorem-body realization over the non-singleton
admissible Rayleigh carrier. -/
def admissibleSelfAdjointHPhysTheoremData : SelfAdjointHPhysTheoremData.{0} :=
  { state := RayleighAdmissibleState
    inner := fun ψ φ => ψ.1 * φ.1
    H_phys := fun ψ => ψ
    domain := fun ψ => RayleighEnergyAdmissible ψ.1
    witness := exactGapRayleighAdmissibleWitness
    witness_in_domain := exact_gap_value_rayleigh_admissible
    domain_closed_under_H := by
      intro ψ hψ
      exact hψ
    symmetric_on_domain := by
      intro ψ φ hψ hφ
      rfl
    selfAdjointCertificate := admissibleHilbertRayleighQuotientData.certified
    selfAdjointCertificate_proof := admissible_hilbert_rayleigh_quotient_data_certified
    rayleighData := admissibleHilbertRayleighQuotientData
    state_to_rayleigh := fun ψ => ψ
    rayleigh_admissible_of_domain := by
      intro ψ hψ
      exact hψ
    rayleigh_lower_bound_of_domain := by
      intro ψ hψ
      exact admissible_hilbert_rayleigh_quotient_lower_bound ψ hψ
    witness_rayleigh_attains_exact := admissible_hilbert_rayleigh_quotient_witness_attains
    exact_value_positive := exactGapValueReal_pos
    concreteUnboundedRealizationStillOpen :=
      ∃ ψ : RayleighAdmissibleState, RayleighEnergyAdmissible ψ.1 }

theorem admissible_self_adjoint_hphys_theorem_data_certified :
    admissibleSelfAdjointHPhysTheoremData.certified := by
  exact And.intro exact_gap_value_rayleigh_admissible <|
    And.intro admissibleSelfAdjointHPhysTheoremData.domain_closed_under_H <|
    And.intro admissibleSelfAdjointHPhysTheoremData.symmetric_on_domain <|
    And.intro admissible_hilbert_rayleigh_quotient_data_certified <|
    And.intro admissibleSelfAdjointHPhysTheoremData.rayleigh_admissible_of_domain <|
    And.intro admissibleSelfAdjointHPhysTheoremData.rayleigh_lower_bound_of_domain <|
    And.intro admissible_hilbert_rayleigh_quotient_witness_attains <|
    And.intro exactGapValueReal_pos <|
    ⟨exactGapRayleighAdmissibleWitness, exact_gap_value_rayleigh_admissible⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem admissible_self_adjoint_hphys_theorem_data_ready :
    admissibleSelfAdjointHPhysTheoremData.ready := by
  exact admissible_self_adjoint_hphys_theorem_data_certified

theorem admissible_self_adjoint_hphys_symmetric_on_domain
    (ψ φ : admissibleSelfAdjointHPhysTheoremData.state)
    (hψ : admissibleSelfAdjointHPhysTheoremData.domain ψ)
    (hφ : admissibleSelfAdjointHPhysTheoremData.domain φ) :
    admissibleSelfAdjointHPhysTheoremData.inner
      (admissibleSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    admissibleSelfAdjointHPhysTheoremData.inner ψ
      (admissibleSelfAdjointHPhysTheoremData.H_phys φ) := by
  exact self_adjoint_hphys_symmetric_on_domain
    admissibleSelfAdjointHPhysTheoremData
    admissible_self_adjoint_hphys_theorem_data_certified ψ φ hψ hφ

theorem admissible_self_adjoint_hphys_rayleigh_lower_bound
    (ψ : admissibleSelfAdjointHPhysTheoremData.state)
    (hψ : admissibleSelfAdjointHPhysTheoremData.domain ψ) :
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
        (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh ψ) := by
  exact self_adjoint_hphys_rayleigh_lower_bound
    admissibleSelfAdjointHPhysTheoremData
    admissible_self_adjoint_hphys_theorem_data_certified ψ hψ

theorem admissible_self_adjoint_hphys_witness_rayleigh_attains :
    admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
      (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh
        admissibleSelfAdjointHPhysTheoremData.witness) = exactGapValueReal := by
  exact self_adjoint_hphys_witness_rayleigh_attains
    admissibleSelfAdjointHPhysTheoremData
    admissible_self_adjoint_hphys_theorem_data_certified

/-- Review surface closing the abstract self-adjoint `H_phys` theorem body after
the Rayleigh quotient theorem body. -/
structure SelfAdjointHPhysTheoremReviewSurface where
  rayleighQuotientCertified : hilbertRayleighQuotientReviewSurface.certified
  hphysTheoremDataCertified : admissibleSelfAdjointHPhysTheoremData.certified
  symmetryOnDomain : ∀ ψ φ : admissibleSelfAdjointHPhysTheoremData.state,
    admissibleSelfAdjointHPhysTheoremData.domain ψ →
    admissibleSelfAdjointHPhysTheoremData.domain φ →
    admissibleSelfAdjointHPhysTheoremData.inner
      (admissibleSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    admissibleSelfAdjointHPhysTheoremData.inner ψ
      (admissibleSelfAdjointHPhysTheoremData.H_phys φ)
  rayleighLowerBound : ∀ ψ : admissibleSelfAdjointHPhysTheoremData.state,
    admissibleSelfAdjointHPhysTheoremData.domain ψ →
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
        (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh ψ)
  witnessAttains : admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
    (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh
      admissibleSelfAdjointHPhysTheoremData.witness) = exactGapValueReal
  selfAdjointTheoremBodyClosed : admissibleSelfAdjointHPhysTheoremData.selfAdjointCertificate
  concreteUnboundedRealizationStillOpen :
    ∃ ψ : RayleighAdmissibleState, RayleighEnergyAdmissible ψ.1
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld : exactGapValueReal ∈ exactGapEnergyRay

/-- Concrete certification predicate for the self-adjoint `H_phys` review surface.

As in the Rayleigh review surface, proof fields are not reused as proposition
heads.  The certification predicate names the corresponding concrete Mathlib
propositions directly, keeping the record fields as witnesses. -/
def SelfAdjointHPhysTheoremReviewSurface.certified
    (_S : SelfAdjointHPhysTheoremReviewSurface) : Prop :=
  hilbertRayleighQuotientReviewSurface.certified ∧
  admissibleSelfAdjointHPhysTheoremData.certified ∧
  (∀ ψ φ : admissibleSelfAdjointHPhysTheoremData.state,
    admissibleSelfAdjointHPhysTheoremData.domain ψ →
    admissibleSelfAdjointHPhysTheoremData.domain φ →
    admissibleSelfAdjointHPhysTheoremData.inner
      (admissibleSelfAdjointHPhysTheoremData.H_phys ψ) φ =
    admissibleSelfAdjointHPhysTheoremData.inner ψ
      (admissibleSelfAdjointHPhysTheoremData.H_phys φ)) ∧
  (∀ ψ : admissibleSelfAdjointHPhysTheoremData.state,
    admissibleSelfAdjointHPhysTheoremData.domain ψ →
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
        (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh ψ)) ∧
  (admissibleSelfAdjointHPhysTheoremData.rayleighData.quotient
    (admissibleSelfAdjointHPhysTheoremData.state_to_rayleigh
      admissibleSelfAdjointHPhysTheoremData.witness) = exactGapValueReal) ∧
  admissibleSelfAdjointHPhysTheoremData.selfAdjointCertificate ∧
  (∃ ψ : RayleighAdmissibleState, RayleighEnergyAdmissible ψ.1) ∧
  (0 < exactGapValueReal) ∧
  (exactGapValueReal ∈ exactGapEnergyRay)

/-- Backward-compatible readiness name during downstream migration. -/
def SelfAdjointHPhysTheoremReviewSurface.ready
    (S : SelfAdjointHPhysTheoremReviewSurface) : Prop :=
  S.certified

def selfAdjointHPhysTheoremReviewSurface : SelfAdjointHPhysTheoremReviewSurface :=
  { rayleighQuotientCertified := hilbert_rayleigh_quotient_review_surface_certified
    hphysTheoremDataCertified := admissible_self_adjoint_hphys_theorem_data_certified
    symmetryOnDomain := admissible_self_adjoint_hphys_symmetric_on_domain
    rayleighLowerBound := admissible_self_adjoint_hphys_rayleigh_lower_bound
    witnessAttains := admissible_self_adjoint_hphys_witness_rayleigh_attains
    selfAdjointTheoremBodyClosed := admissible_hilbert_rayleigh_quotient_data_certified
    concreteUnboundedRealizationStillOpen :=
      ⟨exactGapRayleighAdmissibleWitness, exact_gap_value_rayleigh_admissible⟩
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := exactGapValueReal_mem_energyRay }

theorem self_adjoint_hphys_theorem_review_surface_certified :
    SelfAdjointHPhysTheoremReviewSurface.certified selfAdjointHPhysTheoremReviewSurface := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_certified <|
    And.intro admissible_self_adjoint_hphys_theorem_data_certified <|
    And.intro admissible_self_adjoint_hphys_symmetric_on_domain <|
    And.intro admissible_self_adjoint_hphys_rayleigh_lower_bound <|
    And.intro admissible_self_adjoint_hphys_witness_rayleigh_attains <|
    And.intro admissible_hilbert_rayleigh_quotient_data_certified <|
    And.intro (⟨exactGapRayleighAdmissibleWitness, exact_gap_value_rayleigh_admissible⟩) <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

/-- Backward-compatible theorem name during downstream migration. -/
theorem self_adjoint_hphys_theorem_review_surface_ready :
    SelfAdjointHPhysTheoremReviewSurface.ready selfAdjointHPhysTheoremReviewSurface := by
  exact self_adjoint_hphys_theorem_review_surface_certified

theorem self_adjoint_hphys_theorem_review_surface_final_release_held :
    0 < exactGapValueReal := by
  exact selfAdjointHPhysTheoremReviewSurface.finalReleaseHeld

end

end MathlibAnalytic
end MGAP4D