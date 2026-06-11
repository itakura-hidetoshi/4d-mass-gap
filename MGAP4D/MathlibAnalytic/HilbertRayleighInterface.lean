import MGAP4D.MathlibAnalytic.ExactGapAnalyticRealClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract Hilbert/Rayleigh interface for the next analytic layer. -/
structure HilbertRayleighInterface where
  state : Type
  rayleighEnergy : state → ℝ
  admissible : state → Prop
  witness : state
  witness_admissible : admissible witness
  witness_energy_eq_exact : rayleighEnergy witness = exactGapValueReal
  lower_bound : ∀ ψ, admissible ψ → exactGapValueReal ≤ rayleighEnergy ψ
  exact_value_positive : 0 < exactGapValueReal
  witness_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay

/-- The interface-level exact-gap attainment predicate. -/
def HilbertRayleighInterface.attainsExactGap
    (I : HilbertRayleighInterface) (ψ : I.state) : Prop :=
  I.admissible ψ ∧ I.rayleighEnergy ψ = exactGapValueReal

/-- A ready predicate for the abstract Hilbert/Rayleigh interface. -/
def HilbertRayleighInterface.ready (I : HilbertRayleighInterface) : Prop :=
  I.admissible I.witness ∧
  I.rayleighEnergy I.witness = exactGapValueReal ∧
  (∀ ψ, I.admissible ψ → exactGapValueReal ≤ I.rayleighEnergy ψ) ∧
  0 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay

/-- A minimal singleton-state realization of the abstract interface. -/
noncomputable def singletonHilbertRayleighInterface : HilbertRayleighInterface :=
  { state := PUnit
    rayleighEnergy := fun _ => exactGapValueReal
    admissible := fun _ => exactGapValueReal ∈ exactGapEnergyRay
    witness := PUnit.unit
    witness_admissible := exactGapValueReal_mem_energyRay
    witness_energy_eq_exact := rfl
    lower_bound := by
      intro _ _
      exact le_rfl
    exact_value_positive := exactGapValueReal_pos
    witness_in_energyRay := exactGapValueReal_mem_energyRay }

theorem singleton_hilbert_rayleigh_interface_ready :
    singletonHilbertRayleighInterface.ready := by
  exact And.intro exactGapValueReal_mem_energyRay <|
    And.intro rfl <|
    And.intro (by
      intro _ _
      exact le_rfl) <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

theorem singleton_hilbert_rayleigh_interface_attains :
    singletonHilbertRayleighInterface.attainsExactGap
      singletonHilbertRayleighInterface.witness := by
  exact And.intro exactGapValueReal_mem_energyRay rfl

theorem singleton_hilbert_rayleigh_interface_lower_bound
    (ψ : singletonHilbertRayleighInterface.state)
    (_hψ : singletonHilbertRayleighInterface.admissible ψ) :
    exactGapValueReal ≤ singletonHilbertRayleighInterface.rayleighEnergy ψ := by
  exact le_rfl

/-- Review surface connecting the real analytic closure to the abstract Hilbert/Rayleigh interface. -/
structure HilbertRayleighInterfaceReviewSurface where
  realClosureReady : exactGapAnalyticRealClosure.ready
  interfaceReady : singletonHilbertRayleighInterface.ready
  witnessAttains : singletonHilbertRayleighInterface.attainsExactGap
    singletonHilbertRayleighInterface.witness
  lowerBoundCompatible : ∀ ψ, singletonHilbertRayleighInterface.admissible ψ →
    exactGapValueReal ≤ singletonHilbertRayleighInterface.rayleighEnergy ψ
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  exactValue_attains_rayleigh : RayleighAttainsExactGap exactGapValueReal

def HilbertRayleighInterfaceReviewSurface.ready
    (_S : HilbertRayleighInterfaceReviewSurface) : Prop :=
  exactGapAnalyticRealClosure.ready ∧
  singletonHilbertRayleighInterface.ready ∧
  singletonHilbertRayleighInterface.attainsExactGap
    singletonHilbertRayleighInterface.witness ∧
  (∀ ψ, singletonHilbertRayleighInterface.admissible ψ →
    exactGapValueReal ≤ singletonHilbertRayleighInterface.rayleighEnergy ψ) ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  RayleighAttainsExactGap exactGapValueReal

noncomputable def hilbertRayleighInterfaceReviewSurface :
    HilbertRayleighInterfaceReviewSurface :=
  { realClosureReady := exact_gap_analytic_real_closure_ready
    interfaceReady := singleton_hilbert_rayleigh_interface_ready
    witnessAttains := singleton_hilbert_rayleigh_interface_attains
    lowerBoundCompatible := singleton_hilbert_rayleigh_interface_lower_bound
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray
    exactValue_attains_rayleigh := exact_gap_value_attains_rayleigh }

theorem hilbert_rayleigh_interface_review_surface_ready :
    hilbertRayleighInterfaceReviewSurface.ready := by
  exact And.intro exact_gap_analytic_real_closure_ready <|
    And.intro singleton_hilbert_rayleigh_interface_ready <|
    And.intro singleton_hilbert_rayleigh_interface_attains <|
    And.intro singleton_hilbert_rayleigh_interface_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_mem_positive_ray exact_gap_value_attains_rayleigh

theorem hilbert_rayleigh_interface_review_surface_exact_value_in_energyRay :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

end MathlibAnalytic
end MGAP4D
