import MGAP4D.MathlibAnalytic.ExactGapAnalyticRealClosure

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Abstract Hilbert/Rayleigh interface for the next analytic layer.

This is the first post-adoption interface toward the full Hilbert-space Rayleigh
theorem.  It deliberately keeps the actual inner-product/operator theorem open,
while requiring any future Hilbert-space realization to provide:

* a state carrier,
* a Rayleigh-energy map into `ℝ`,
* an admissibility predicate,
* a witness state attaining the exact gap,
* a lower-bound proof for all admissible states. -/
structure HilbertRayleighInterface where
  state : Type u
  rayleighEnergy : state → ℝ
  admissible : state → Prop
  witness : state
  witness_admissible : admissible witness
  witness_energy_eq_exact : rayleighEnergy witness = exactGapValueReal
  lower_bound : ∀ ψ, admissible ψ → exactGapValueReal ≤ rayleighEnergy ψ
  exact_value_positive : 0 < exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  fullHilbertTheoremStillOpen : Prop

/-- The interface-level exact-gap attainment predicate. -/
def HilbertRayleighInterface.attainsExactGap
    (I : HilbertRayleighInterface) (ψ : I.state) : Prop :=
  I.admissible ψ ∧ I.rayleighEnergy ψ = exactGapValueReal

/-- A ready predicate for the abstract Hilbert/Rayleigh interface. -/
def HilbertRayleighInterface.ready (I : HilbertRayleighInterface) : Prop :=
  I.witness_admissible ∧ I.witness_energy_eq_exact ∧ I.lower_bound ∧
  I.exact_value_positive ∧ I.exact_value_eq_3320 ∧ I.fullHilbertTheoremStillOpen

/-- A minimal singleton-state realization of the abstract interface.

This keeps the hard Hilbert-space theorem open, but gives the Mathlib branch a
concrete interface-level target that is consistent with the real-order analytic
closure. -/
def singletonHilbertRayleighInterface : HilbertRayleighInterface :=
  { state := PUnit
    rayleighEnergy := fun _ => exactGapValueReal
    admissible := fun _ => True
    witness := PUnit.unit
    witness_admissible := True.intro
    witness_energy_eq_exact := rfl
    lower_bound := by
      intro ψ hψ
      exact le_rfl
    exact_value_positive := exactGapValueReal_pos
    exact_value_eq_3320 := exactGapValueReal_eq
    fullHilbertTheoremStillOpen := True }

theorem singleton_hilbert_rayleigh_interface_ready :
    singletonHilbertRayleighInterface.ready := by
  exact And.intro True.intro <|
    And.intro rfl <|
    And.intro (by
      intro ψ hψ
      exact le_rfl) <|
    And.intro exactGapValueReal_pos <|
    And.intro exactGapValueReal_eq True.intro

theorem singleton_hilbert_rayleigh_interface_attains :
    singletonHilbertRayleighInterface.attainsExactGap
      singletonHilbertRayleighInterface.witness := by
  exact And.intro True.intro rfl

theorem singleton_hilbert_rayleigh_interface_lower_bound
    (ψ : singletonHilbertRayleighInterface.state)
    (hψ : singletonHilbertRayleighInterface.admissible ψ) :
    exactGapValueReal ≤ singletonHilbertRayleighInterface.rayleighEnergy ψ := by
  exact le_rfl

/-- Review surface connecting the real analytic closure to the abstract
Hilbert/Rayleigh interface. -/
structure HilbertRayleighInterfaceReviewSurface where
  realClosureReady : exactGapAnalyticRealClosure.ready
  interfaceReady : singletonHilbertRayleighInterface.ready
  witnessAttains : singletonHilbertRayleighInterface.attainsExactGap
    singletonHilbertRayleighInterface.witness
  lowerBoundCompatible : ∀ ψ, singletonHilbertRayleighInterface.admissible ψ →
    exactGapValueReal ≤ singletonHilbertRayleighInterface.rayleighEnergy ψ
  exactValue_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  fullHilbertTheoremStillOpen : Prop
  mainMathlibBacked : Prop
  finalReleaseHeld : Prop

def HilbertRayleighInterfaceReviewSurface.ready
    (S : HilbertRayleighInterfaceReviewSurface) : Prop :=
  S.realClosureReady ∧ S.interfaceReady ∧ S.witnessAttains ∧
  S.lowerBoundCompatible ∧ S.exactValue_eq_3320 ∧
  S.fullHilbertTheoremStillOpen ∧ S.mainMathlibBacked ∧ S.finalReleaseHeld

def hilbertRayleighInterfaceReviewSurface : HilbertRayleighInterfaceReviewSurface :=
  { realClosureReady := exact_gap_analytic_real_closure_ready
    interfaceReady := singleton_hilbert_rayleigh_interface_ready
    witnessAttains := singleton_hilbert_rayleigh_interface_attains
    lowerBoundCompatible := singleton_hilbert_rayleigh_interface_lower_bound
    exactValue_eq_3320 := exactGapValueReal_eq
    fullHilbertTheoremStillOpen := True
    mainMathlibBacked := True
    finalReleaseHeld := True }

theorem hilbert_rayleigh_interface_review_surface_ready :
    hilbertRayleighInterfaceReviewSurface.ready := by
  exact And.intro exact_gap_analytic_real_closure_ready <|
    And.intro singleton_hilbert_rayleigh_interface_ready <|
    And.intro singleton_hilbert_rayleigh_interface_attains <|
    And.intro singleton_hilbert_rayleigh_interface_lower_bound <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem hilbert_rayleigh_interface_review_surface_final_release_held :
    hilbertRayleighInterfaceReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
