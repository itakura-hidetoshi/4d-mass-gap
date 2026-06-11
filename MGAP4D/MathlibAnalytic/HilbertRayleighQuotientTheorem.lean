import MGAP4D.MathlibAnalytic.ExactGapPostInterfaceResidualMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- Abstract Rayleigh-quotient data for the Hilbert theorem body.

This is the first theorem-body step beyond the interface layer. It makes the
Rayleigh quotient explicit as numerator divided by norm squared, keeps a
positive-norm admissibility condition, and records the lower-bound theorem body
for all admissible states.  It deliberately carries no upstream `33/20` theorem;
that numeric equality is first exported at the R6 spectral-origin surface. -/
structure HilbertRayleighQuotientData where
  state : Type u
  numerator : state → ℝ
  normSq : state → ℝ
  admissible : state → Prop
  witness : state
  witness_admissible : admissible witness
  witness_normSq_pos : 0 < normSq witness
  normSq_pos_of_admissible : ∀ ψ, admissible ψ → 0 < normSq ψ
  quotient : state → ℝ
  quotient_def : ∀ ψ, quotient ψ = numerator ψ / normSq ψ
  witness_quotient_eq_exact : quotient witness = exactGapValueReal
  quotient_lower_bound : ∀ ψ, admissible ψ → exactGapValueReal ≤ quotient ψ
  exact_value_positive : 0 < exactGapValueReal

/-- Concrete certification predicate for the Rayleigh-quotient theorem body. -/
def HilbertRayleighQuotientData.certified (D : HilbertRayleighQuotientData) : Prop :=
  D.admissible D.witness ∧ 0 < D.normSq D.witness ∧
  (∀ ψ, D.admissible ψ → 0 < D.normSq ψ) ∧
  (∀ ψ, D.quotient ψ = D.numerator ψ / D.normSq ψ) ∧
  D.quotient D.witness = exactGapValueReal ∧
  (∀ ψ, D.admissible ψ → exactGapValueReal ≤ D.quotient ψ) ∧
  0 < exactGapValueReal

/-- Backward-compatible readiness name during downstream migration. -/
def HilbertRayleighQuotientData.ready (D : HilbertRayleighQuotientData) : Prop :=
  D.certified

/-- The Rayleigh quotient associated to the data. -/
def HilbertRayleighQuotientData.rayleighQuotient
    (D : HilbertRayleighQuotientData) (ψ : D.state) : ℝ :=
  D.numerator ψ / D.normSq ψ

/-- Any quotient satisfying the data's quotient definition agrees with the
explicit quotient expression. -/
theorem hilbert_rayleigh_quotient_eq
    (D : HilbertRayleighQuotientData) (ψ : D.state) :
    D.quotient ψ = D.rayleighQuotient ψ := by
  exact D.quotient_def ψ

/-- Abstract Hilbert/Rayleigh quotient lower-bound theorem body. -/
theorem hilbert_rayleigh_quotient_lower_bound
    (D : HilbertRayleighQuotientData) (hD : D.certified)
    (ψ : D.state) (hψ : D.admissible ψ) :
    exactGapValueReal ≤ D.quotient ψ := by
  rcases hD with ⟨_, _, _, _, _, hLower, _⟩
  exact hLower ψ hψ

/-- Abstract exact-gap attainment for the Rayleigh quotient witness. -/
theorem hilbert_rayleigh_quotient_witness_attains
    (D : HilbertRayleighQuotientData) (hD : D.certified) :
    D.quotient D.witness = exactGapValueReal := by
  rcases hD with ⟨_, _, _, _, hWitness, _, _⟩
  exact hWitness

/-- Abstract positivity of the admissible denominator. -/
theorem hilbert_rayleigh_quotient_normSq_pos
    (D : HilbertRayleighQuotientData) (hD : D.certified)
    (ψ : D.state) (hψ : D.admissible ψ) :
    0 < D.normSq ψ := by
  rcases hD with ⟨_, _, hNorm, _, _, _, _⟩
  exact hNorm ψ hψ

/-- Rayleigh quotient data over the non-singleton admissible energy carrier.

The state space is the actual subtype of admissible Rayleigh energies.  The
quotient is the underlying energy itself, realized as `energy / 1`, so the lower
bound is inherited from `rayleigh_energy_admissible_lower_bound` rather than from
any singleton or propositional placeholder. -/
def admissibleHilbertRayleighQuotientData : HilbertRayleighQuotientData.{0} :=
  { state := RayleighAdmissibleState
    numerator := fun ψ => ψ.1
    normSq := fun _ => 1
    admissible := fun ψ => RayleighEnergyAdmissible ψ.1
    witness := exactGapRayleighAdmissibleWitness
    witness_admissible := exact_gap_value_rayleigh_admissible
    witness_normSq_pos := by norm_num
    normSq_pos_of_admissible := by
      intro ψ hψ
      norm_num
    quotient := fun ψ => ψ.1
    quotient_def := by
      intro ψ
      simp
    witness_quotient_eq_exact := rfl
    quotient_lower_bound := by
      intro ψ hψ
      exact rayleigh_energy_admissible_lower_bound ψ.1 hψ
    exact_value_positive := exactGapValueReal_pos }

theorem admissible_hilbert_rayleigh_quotient_data_certified :
    admissibleHilbertRayleighQuotientData.certified := by
  exact And.intro exact_gap_value_rayleigh_admissible <|
    And.intro admissibleHilbertRayleighQuotientData.witness_normSq_pos <|
    And.intro admissibleHilbertRayleighQuotientData.normSq_pos_of_admissible <|
    And.intro admissibleHilbertRayleighQuotientData.quotient_def <|
    And.intro admissibleHilbertRayleighQuotientData.witness_quotient_eq_exact <|
    And.intro admissibleHilbertRayleighQuotientData.quotient_lower_bound <|
    exactGapValueReal_pos

/-- Backward-compatible theorem name during downstream migration. -/
theorem admissible_hilbert_rayleigh_quotient_data_ready :
    admissibleHilbertRayleighQuotientData.ready := by
  exact admissible_hilbert_rayleigh_quotient_data_certified

theorem admissible_hilbert_rayleigh_quotient_lower_bound
    (ψ : admissibleHilbertRayleighQuotientData.state)
    (hψ : admissibleHilbertRayleighQuotientData.admissible ψ) :
    exactGapValueReal ≤ admissibleHilbertRayleighQuotientData.quotient ψ := by
  exact hilbert_rayleigh_quotient_lower_bound
    admissibleHilbertRayleighQuotientData
    admissible_hilbert_rayleigh_quotient_data_certified ψ hψ

theorem admissible_hilbert_rayleigh_quotient_witness_attains :
    admissibleHilbertRayleighQuotientData.quotient
      admissibleHilbertRayleighQuotientData.witness = exactGapValueReal := by
  exact hilbert_rayleigh_quotient_witness_attains
    admissibleHilbertRayleighQuotientData
    admissible_hilbert_rayleigh_quotient_data_certified

/-- Review surface closing the Rayleigh quotient theorem body after the
post-interface residual map. -/
structure HilbertRayleighQuotientReviewSurface where
  postInterfaceResidualMapCertified : exactGapPostInterfaceResidualMap.certified
  quotientDataCertified : admissibleHilbertRayleighQuotientData.certified
  quotientLowerBound : ∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.admissible ψ →
      exactGapValueReal ≤ admissibleHilbertRayleighQuotientData.quotient ψ
  witnessAttains : admissibleHilbertRayleighQuotientData.quotient
    admissibleHilbertRayleighQuotientData.witness = exactGapValueReal
  quotientDefinitionVisible : ∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.quotient ψ =
      admissibleHilbertRayleighQuotientData.numerator ψ /
        admissibleHilbertRayleighQuotientData.normSq ψ
  admissibleNormPositive : ∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.admissible ψ →
      0 < admissibleHilbertRayleighQuotientData.normSq ψ
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld : exactGapValueReal ∈ exactGapEnergyRay

/-- Concrete certification predicate for the Rayleigh quotient review surface.

The predicate is a conjunction of propositions.  The fields `S.finalReleaseHeld`
and `S.publicBoundaryHeld` are proof terms, so they are intentionally not used as
proposition heads inside the conjunction. -/
def HilbertRayleighQuotientReviewSurface.certified
    (_S : HilbertRayleighQuotientReviewSurface) : Prop :=
  exactGapPostInterfaceResidualMap.certified ∧
  admissibleHilbertRayleighQuotientData.certified ∧
  (∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.admissible ψ →
      exactGapValueReal ≤ admissibleHilbertRayleighQuotientData.quotient ψ) ∧
  (admissibleHilbertRayleighQuotientData.quotient
    admissibleHilbertRayleighQuotientData.witness = exactGapValueReal) ∧
  (∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.quotient ψ =
      admissibleHilbertRayleighQuotientData.numerator ψ /
        admissibleHilbertRayleighQuotientData.normSq ψ) ∧
  (∀ ψ : admissibleHilbertRayleighQuotientData.state,
    admissibleHilbertRayleighQuotientData.admissible ψ →
      0 < admissibleHilbertRayleighQuotientData.normSq ψ) ∧
  (0 < exactGapValueReal) ∧
  (exactGapValueReal ∈ exactGapEnergyRay)

/-- Backward-compatible readiness name during downstream migration. -/
def HilbertRayleighQuotientReviewSurface.ready
    (S : HilbertRayleighQuotientReviewSurface) : Prop :=
  S.certified

def hilbertRayleighQuotientReviewSurface : HilbertRayleighQuotientReviewSurface :=
  { postInterfaceResidualMapCertified := exact_gap_post_interface_residual_map_certified
    quotientDataCertified := admissible_hilbert_rayleigh_quotient_data_certified
    quotientLowerBound := admissible_hilbert_rayleigh_quotient_lower_bound
    witnessAttains := admissible_hilbert_rayleigh_quotient_witness_attains
    quotientDefinitionVisible := admissibleHilbertRayleighQuotientData.quotient_def
    admissibleNormPositive := admissibleHilbertRayleighQuotientData.normSq_pos_of_admissible
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := exactGapValueReal_mem_energyRay }

theorem hilbert_rayleigh_quotient_review_surface_certified :
    hilbertRayleighQuotientReviewSurface.certified := by
  exact And.intro exact_gap_post_interface_residual_map_certified <|
    And.intro admissible_hilbert_rayleigh_quotient_data_certified <|
    And.intro admissible_hilbert_rayleigh_quotient_lower_bound <|
    And.intro admissible_hilbert_rayleigh_quotient_witness_attains <|
    And.intro admissibleHilbertRayleighQuotientData.quotient_def <|
    And.intro admissibleHilbertRayleighQuotientData.normSq_pos_of_admissible <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

/-- Backward-compatible theorem name during downstream migration. -/
theorem hilbert_rayleigh_quotient_review_surface_ready :
    hilbertRayleighQuotientReviewSurface.ready := by
  exact hilbert_rayleigh_quotient_review_surface_certified

theorem hilbert_rayleigh_quotient_review_surface_final_release_held :
    0 < exactGapValueReal := by
  exact hilbertRayleighQuotientReviewSurface.finalReleaseHeld

end

end MathlibAnalytic
end MGAP4D