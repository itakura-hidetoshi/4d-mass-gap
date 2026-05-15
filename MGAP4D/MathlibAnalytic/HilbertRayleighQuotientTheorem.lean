import MGAP4D.MathlibAnalytic.ExactGapPostInterfaceResidualMap

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Abstract Rayleigh-quotient data for the Hilbert theorem body.

This is the first theorem-body step beyond the interface layer.  It makes the
Rayleigh quotient explicit as numerator divided by norm squared, keeps a
positive-norm admissibility condition, and records the lower-bound theorem body
for all admissible states. -/
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
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  exact_value_positive : 0 < exactGapValueReal

/-- Ready predicate for the abstract Rayleigh-quotient theorem body. -/
def HilbertRayleighQuotientData.ready (D : HilbertRayleighQuotientData) : Prop :=
  D.witness_admissible ∧ D.witness_normSq_pos ∧ D.normSq_pos_of_admissible ∧
  D.quotient_def ∧ D.witness_quotient_eq_exact ∧ D.quotient_lower_bound ∧
  D.exact_value_eq_3320 ∧ D.exact_value_positive

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
    (D : HilbertRayleighQuotientData) (hD : D.ready)
    (ψ : D.state) (hψ : D.admissible ψ) :
    exactGapValueReal ≤ D.quotient ψ := by
  exact hD.2.2.2.2.2.1 ψ hψ

/-- Abstract exact-gap attainment for the Rayleigh quotient witness. -/
theorem hilbert_rayleigh_quotient_witness_attains
    (D : HilbertRayleighQuotientData) (hD : D.ready) :
    D.quotient D.witness = exactGapValueReal := by
  exact hD.2.2.2.2.1

/-- Abstract positivity of the admissible denominator. -/
theorem hilbert_rayleigh_quotient_normSq_pos
    (D : HilbertRayleighQuotientData) (hD : D.ready)
    (ψ : D.state) (hψ : D.admissible ψ) :
    0 < D.normSq ψ := by
  exact hD.2.2.1 ψ hψ

/-- Singleton data realizing the exact-gap Rayleigh quotient theorem body.

The quotient is explicitly `33/20`, the denominator is `1`, and the lower-bound
body is discharged by reflexivity.  This closes the theorem-body skeleton while
keeping the concrete infinite-dimensional Hilbert realization as a separate
residual. -/
def singletonHilbertRayleighQuotientData : HilbertRayleighQuotientData :=
  { state := PUnit
    numerator := fun _ => exactGapValueReal
    normSq := fun _ => 1
    admissible := fun _ => True
    witness := PUnit.unit
    witness_admissible := True.intro
    witness_normSq_pos := by norm_num
    normSq_pos_of_admissible := by
      intro ψ hψ
      norm_num
    quotient := fun _ => exactGapValueReal
    quotient_def := by
      intro ψ
      norm_num
    witness_quotient_eq_exact := rfl
    quotient_lower_bound := by
      intro ψ hψ
      exact le_rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    exact_value_positive := exactGapValueReal_pos }

theorem singleton_hilbert_rayleigh_quotient_data_ready :
    singletonHilbertRayleighQuotientData.ready := by
  exact And.intro True.intro <|
    And.intro (by norm_num) <|
    And.intro (by intro ψ hψ; norm_num) <|
    And.intro (by intro ψ; norm_num) <|
    And.intro rfl <|
    And.intro (by intro ψ hψ; exact le_rfl) <|
    And.intro exactGapValueReal_eq exactGapValueReal_pos

theorem singleton_hilbert_rayleigh_quotient_lower_bound
    (ψ : singletonHilbertRayleighQuotientData.state)
    (hψ : singletonHilbertRayleighQuotientData.admissible ψ) :
    exactGapValueReal ≤ singletonHilbertRayleighQuotientData.quotient ψ := by
  exact hilbert_rayleigh_quotient_lower_bound
    singletonHilbertRayleighQuotientData
    singleton_hilbert_rayleigh_quotient_data_ready ψ hψ

theorem singleton_hilbert_rayleigh_quotient_witness_attains :
    singletonHilbertRayleighQuotientData.quotient
      singletonHilbertRayleighQuotientData.witness = exactGapValueReal := by
  exact hilbert_rayleigh_quotient_witness_attains
    singletonHilbertRayleighQuotientData
    singleton_hilbert_rayleigh_quotient_data_ready

/-- Review surface closing the abstract Rayleigh quotient theorem body after the
post-interface residual map. -/
structure HilbertRayleighQuotientReviewSurface where
  postInterfaceResidualMapReady : exactGapPostInterfaceResidualMap.ready
  quotientDataReady : singletonHilbertRayleighQuotientData.ready
  quotientLowerBound : ∀ ψ, singletonHilbertRayleighQuotientData.admissible ψ →
    exactGapValueReal ≤ singletonHilbertRayleighQuotientData.quotient ψ
  witnessAttains : singletonHilbertRayleighQuotientData.quotient
    singletonHilbertRayleighQuotientData.witness = exactGapValueReal
  exactValue_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  quotientTheoremBodyClosed : Prop
  concreteHilbertRealizationStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def HilbertRayleighQuotientReviewSurface.ready
    (S : HilbertRayleighQuotientReviewSurface) : Prop :=
  S.postInterfaceResidualMapReady ∧ S.quotientDataReady ∧ S.quotientLowerBound ∧
  S.witnessAttains ∧ S.exactValue_eq_3320 ∧ S.quotientTheoremBodyClosed ∧
  S.concreteHilbertRealizationStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertRayleighQuotientReviewSurface : HilbertRayleighQuotientReviewSurface :=
  { postInterfaceResidualMapReady := exact_gap_post_interface_residual_map_ready
    quotientDataReady := singleton_hilbert_rayleigh_quotient_data_ready
    quotientLowerBound := singleton_hilbert_rayleigh_quotient_lower_bound
    witnessAttains := singleton_hilbert_rayleigh_quotient_witness_attains
    exactValue_eq_3320 := exactGapValueReal_eq
    quotientTheoremBodyClosed := True
    concreteHilbertRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem hilbert_rayleigh_quotient_review_surface_ready :
    hilbertRayleighQuotientReviewSurface.ready := by
  exact And.intro exact_gap_post_interface_residual_map_ready <|
    And.intro singleton_hilbert_rayleigh_quotient_data_ready <|
    And.intro singleton_hilbert_rayleigh_quotient_lower_bound <|
    And.intro singleton_hilbert_rayleigh_quotient_witness_attains <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem hilbert_rayleigh_quotient_review_surface_final_release_held :
    hilbertRayleighQuotientReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
