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

/-- Concrete certification predicate for the Hilbert/Rayleigh interface. -/
def HilbertRayleighInterface.certified (I : HilbertRayleighInterface) : Prop :=
  I.admissible I.witness ∧
  I.rayleighEnergy I.witness = exactGapValueReal ∧
  (∀ ψ, I.admissible ψ → exactGapValueReal ≤ I.rayleighEnergy ψ) ∧
  0 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay

/-- Backward-compatible readiness name during downstream migration. -/
def HilbertRayleighInterface.ready (I : HilbertRayleighInterface) : Prop :=
  I.certified

/-- Non-singleton Rayleigh carrier: all real energies satisfying the admissible
Rayleigh predicate. -/
def RayleighAdmissibleState : Type :=
  { energy : ℝ // RayleighEnergyAdmissible energy }

/-- Canonical exact-gap witness inside the admissible Rayleigh carrier. -/
noncomputable def exactGapRayleighAdmissibleWitness : RayleighAdmissibleState :=
  ⟨exactGapValueReal, exact_gap_value_rayleigh_admissible⟩

/-- Mathlib-backed admissible-state realization of the abstract interface.

This replaces the former `PUnit` singleton bridge.  The state type is now the
actual subtype of admissible Rayleigh energies, and admissibility is the Rayleigh
predicate on the underlying energy. -/
noncomputable def admissibleHilbertRayleighInterface : HilbertRayleighInterface :=
  { state := RayleighAdmissibleState
    rayleighEnergy := fun ψ => ψ.1
    admissible := fun ψ => RayleighEnergyAdmissible ψ.1
    witness := exactGapRayleighAdmissibleWitness
    witness_admissible := exact_gap_value_rayleigh_admissible
    witness_energy_eq_exact := rfl
    lower_bound := by
      intro ψ hψ
      exact rayleigh_energy_admissible_lower_bound ψ.1 hψ
    exact_value_positive := exactGapValueReal_pos
    witness_in_energyRay := exactGapValueReal_mem_energyRay }

theorem admissible_hilbert_rayleigh_interface_certified :
    admissibleHilbertRayleighInterface.certified := by
  exact And.intro exact_gap_value_rayleigh_admissible <|
    And.intro rfl <|
    And.intro (by
      intro ψ hψ
      exact rayleigh_energy_admissible_lower_bound ψ.1 hψ) <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

/-- Backward-compatible theorem name during downstream migration. -/
theorem admissible_hilbert_rayleigh_interface_ready :
    admissibleHilbertRayleighInterface.ready := by
  exact admissible_hilbert_rayleigh_interface_certified

theorem admissible_hilbert_rayleigh_interface_attains :
    admissibleHilbertRayleighInterface.attainsExactGap
      admissibleHilbertRayleighInterface.witness := by
  exact And.intro exact_gap_value_rayleigh_admissible rfl

theorem admissible_hilbert_rayleigh_interface_lower_bound
    (ψ : admissibleHilbertRayleighInterface.state)
    (hψ : admissibleHilbertRayleighInterface.admissible ψ) :
    exactGapValueReal ≤ admissibleHilbertRayleighInterface.rayleighEnergy ψ := by
  exact rayleigh_energy_admissible_lower_bound ψ.1 hψ

/-- Review surface connecting the real analytic closure to the abstract Hilbert/Rayleigh interface. -/
structure HilbertRayleighInterfaceReviewSurface where
  realClosureCertified : exactGapAnalyticRealClosure.certified
  interfaceCertified : admissibleHilbertRayleighInterface.certified
  witnessAttains : admissibleHilbertRayleighInterface.attainsExactGap
    admissibleHilbertRayleighInterface.witness
  lowerBoundCompatible : ∀ ψ, admissibleHilbertRayleighInterface.admissible ψ →
    exactGapValueReal ≤ admissibleHilbertRayleighInterface.rayleighEnergy ψ
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  exactValue_attains_rayleigh : RayleighAttainsExactGap exactGapValueReal

/-- Concrete certification predicate for the Hilbert/Rayleigh review surface. -/
def HilbertRayleighInterfaceReviewSurface.certified
    (_S : HilbertRayleighInterfaceReviewSurface) : Prop :=
  exactGapAnalyticRealClosure.certified ∧
  admissibleHilbertRayleighInterface.certified ∧
  admissibleHilbertRayleighInterface.attainsExactGap
    admissibleHilbertRayleighInterface.witness ∧
  (∀ ψ, admissibleHilbertRayleighInterface.admissible ψ →
    exactGapValueReal ≤ admissibleHilbertRayleighInterface.rayleighEnergy ψ) ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  RayleighAttainsExactGap exactGapValueReal

/-- Backward-compatible readiness name during downstream migration. -/
def HilbertRayleighInterfaceReviewSurface.ready
    (S : HilbertRayleighInterfaceReviewSurface) : Prop :=
  S.certified

noncomputable def hilbertRayleighInterfaceReviewSurface :
    HilbertRayleighInterfaceReviewSurface :=
  { realClosureCertified := exact_gap_analytic_real_closure_certified
    interfaceCertified := admissible_hilbert_rayleigh_interface_certified
    witnessAttains := admissible_hilbert_rayleigh_interface_attains
    lowerBoundCompatible := admissible_hilbert_rayleigh_interface_lower_bound
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray
    exactValue_attains_rayleigh := exact_gap_value_attains_rayleigh }

theorem hilbert_rayleigh_interface_review_surface_certified :
    hilbertRayleighInterfaceReviewSurface.certified := by
  exact And.intro exact_gap_analytic_real_closure_certified <|
    And.intro admissible_hilbert_rayleigh_interface_certified <|
    And.intro admissible_hilbert_rayleigh_interface_attains <|
    And.intro admissible_hilbert_rayleigh_interface_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_mem_positive_ray exact_gap_value_attains_rayleigh

/-- Backward-compatible theorem name during downstream migration. -/
theorem hilbert_rayleigh_interface_review_surface_ready :
    hilbertRayleighInterfaceReviewSurface.ready := by
  exact hilbert_rayleigh_interface_review_surface_certified

theorem hilbert_rayleigh_interface_review_surface_exact_value_in_energyRay :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

end MathlibAnalytic
end MGAP4D