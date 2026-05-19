import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteCombinationDomainWitness

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The finite-coordinate seed family for the R2 diagonal-domain candidate.
This is only the algebraic seed family already shown to lie in the candidate
domain.  It intentionally stops before density, graph-core, closed-operator,
self-adjointness, and spectral/PVM claims. -/
def concreteL2R2FiniteSeedFamily : Set ConcreteL2R1HilbertCarrier :=
  {x | ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    x = concreteL2R2FiniteCoordinateCombination s a}

/-- Membership in the finite seed family unfolds to a finite coordinate
combination witness. -/
theorem concrete_l2_r2_finite_seed_family_mem_iff
    (x : ConcreteL2R1HilbertCarrier) :
    x ∈ concreteL2R2FiniteSeedFamily ↔
      ∃ (s : Finset ℕ) (a : ℕ → ℝ),
        x = concreteL2R2FiniteCoordinateCombination s a := by
  rfl

/-- Every finite seed-family vector belongs to the R2 diagonal-domain
candidate. -/
theorem concrete_l2_r2_finite_seed_family_subset_domain
    {x : ConcreteL2R1HilbertCarrier}
    (hx : x ∈ concreteL2R2FiniteSeedFamily) :
    ConcreteL2R2DiagonalDomainCandidate x := by
  rcases hx with ⟨s, a, rfl⟩
  exact concrete_l2_r2_diagonal_domain_candidate_finite_coordinate_combination s a

/-- The finite seed-family subset-domain adapter. -/
def concreteL2R2FiniteSeedFamilySubsetDomainAdapter : Prop :=
  ∀ {x : ConcreteL2R1HilbertCarrier},
    x ∈ concreteL2R2FiniteSeedFamily → ConcreteL2R2DiagonalDomainCandidate x

/-- Adapter theorem for finite seed-family domain membership. -/
theorem concrete_l2_r2_finite_seed_family_subset_domain_adapter_ready :
    concreteL2R2FiniteSeedFamilySubsetDomainAdapter := by
  intro x hx
  exact concrete_l2_r2_finite_seed_family_subset_domain hx

/-- Each explicitly built finite coordinate combination lies in the seed family. -/
theorem concrete_l2_r2_finite_coordinate_combination_mem_seed_family
    (s : Finset ℕ) (a : ℕ → ℝ) :
    concreteL2R2FiniteCoordinateCombination s a ∈ concreteL2R2FiniteSeedFamily := by
  exact ⟨s, a, rfl⟩

/-- Every finite coordinate seed carries an explicit domain witness packet. -/
theorem concrete_l2_r2_finite_seed_family_has_witness
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Nonempty (ConcreteL2R2FiniteCombinationDomainWitness s a) := by
  exact ⟨concreteL2R2FiniteCombinationDomainWitness s a⟩

/-- R2 finite seed-family surface.  This is the PR-ready handoff from finite
coordinate sums to later graph-norm/core analysis. -/
structure ConcreteL2R2FiniteSeedFamilySurface where
  finiteCombinationWitnessReady :
    concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady
  seedFamily : Set ConcreteL2R1HilbertCarrier
  explicitSeedMembership :
    ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      concreteL2R2FiniteCoordinateCombination s a ∈ seedFamily
  seedSubsetDomain :
    ∀ {x : ConcreteL2R1HilbertCarrier},
      x ∈ seedFamily → ConcreteL2R2DiagonalDomainCandidate x
  finiteSeedWitness :
    ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      Nonempty (ConcreteL2R2FiniteCombinationDomainWitness s a)
  boundaryNotDenseDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop

/-- Concrete R2 finite seed-family surface. -/
def concreteL2R2FiniteSeedFamilySurface :
    ConcreteL2R2FiniteSeedFamilySurface :=
  { finiteCombinationWitnessReady :=
      concrete_analytic_spine_l2_r2_finite_combination_domain_witness_surface_ready
    seedFamily := concreteL2R2FiniteSeedFamily
    explicitSeedMembership :=
      concrete_l2_r2_finite_coordinate_combination_mem_seed_family
    seedSubsetDomain := by
      intro x hx
      exact concrete_l2_r2_finite_seed_family_subset_domain hx
    finiteSeedWitness := concrete_l2_r2_finite_seed_family_has_witness
    boundaryNotDenseDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True }

/-- R2 finite seed-family readiness. -/
def concreteAnalyticSpineL2R2FiniteSeedFamilySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady ∧
  concreteL2R2FiniteSeedFamilySubsetDomainAdapter ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotDenseDomainTheorem ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteSeedFamilySurface.boundaryNotPVMConstruction

/-- Readiness theorem for the R2 finite seed-family surface. -/
theorem concrete_analytic_spine_l2_r2_finite_seed_family_surface_ready :
    concreteAnalyticSpineL2R2FiniteSeedFamilySurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteSeedFamilySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_combination_domain_witness_surface_ready <|
      And.intro
        concrete_l2_r2_finite_seed_family_subset_domain_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2 finite seed-family surface. -/
def concreteAnalyticSpineL2R2FiniteSeedFamilyHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteSeedFamilySurfaceReady

/-- Boundary theorem for the R2 finite seed-family surface. -/
theorem concrete_analytic_spine_l2_r2_finite_seed_family_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteSeedFamilyHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_seed_family_surface_ready

end

end MathlibAnalytic
end MGAP4D
