import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomain

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Witness packet for a finite coordinate combination in the R2 diagonal-domain
candidate.  The packet deliberately contains only the finite-support and
domain-membership data already proved in the previous surface; it does not claim
density, graph-core status, closedness, self-adjointness, or spectral/PVM data. -/
structure ConcreteL2R2FiniteCombinationDomainWitness
    (s : Finset ℕ) (a : ℕ → ℝ) where
  vector : ConcreteL2R1HilbertCarrier
  vector_eq : vector = concreteL2R2FiniteCoordinateCombination s a
  weightedSquareFiniteSupport :
    Function.HasFiniteSupport fun n : ℕ =>
      (concreteL2R2WeightedCoordinate vector n) ^ 2
  domainMembership : ConcreteL2R2DiagonalDomainCandidate vector

/-- Canonical witness packet for a finite coordinate combination. -/
def concreteL2R2FiniteCombinationDomainWitness
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ConcreteL2R2FiniteCombinationDomainWitness s a :=
  { vector := concreteL2R2FiniteCoordinateCombination s a
    vector_eq := rfl
    weightedSquareFiniteSupport :=
      concrete_l2_r2_finite_coordinate_combination_weighted_square_has_finite_support s a
    domainMembership :=
      concrete_l2_r2_diagonal_domain_candidate_finite_coordinate_combination s a }

/-- Adapter predicate: every finite coordinate combination has an explicit
support/domain witness packet. -/
def concreteL2R2FiniteCombinationDomainWitnessAdapter : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → ℝ),
    Nonempty (ConcreteL2R2FiniteCombinationDomainWitness s a)

/-- Adapter theorem for finite-combination witness packets. -/
theorem concrete_l2_r2_finite_combination_domain_witness_adapter_ready :
    concreteL2R2FiniteCombinationDomainWitnessAdapter := by
  intro s a
  exact ⟨concreteL2R2FiniteCombinationDomainWitness s a⟩

/-- R2 finite-combination witness surface.  This is a handoff surface from
algebraic finite sums to later domain/core analysis.  The hard boundaries remain
explicit: this packet witnesses membership only, not density or operator-core
closure. -/
structure ConcreteL2R2FiniteCombinationDomainWitnessSurface where
  finiteCoordinateCombinationsReady :
    concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady
  witnessBuilder :
    ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      ConcreteL2R2FiniteCombinationDomainWitness s a
  witnessAdapterReady : concreteL2R2FiniteCombinationDomainWitnessAdapter
  boundaryNotDenseDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop

/-- Concrete R2 finite-combination witness surface. -/
def concreteL2R2FiniteCombinationDomainWitnessSurface :
    ConcreteL2R2FiniteCombinationDomainWitnessSurface :=
  { finiteCoordinateCombinationsReady :=
      concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready
    witnessBuilder := concreteL2R2FiniteCombinationDomainWitness
    witnessAdapterReady :=
      concrete_l2_r2_finite_combination_domain_witness_adapter_ready
    boundaryNotDenseDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True }

/-- Readiness predicate for the R2 finite-combination witness surface. -/
def concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady ∧
  concreteL2R2FiniteCombinationDomainWitnessAdapter ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotDenseDomainTheorem ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteCombinationDomainWitnessSurface.boundaryNotPVMConstruction

/-- Readiness theorem for the R2 finite-combination witness surface. -/
theorem concrete_analytic_spine_l2_r2_finite_combination_domain_witness_surface_ready :
    concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready <|
      And.intro
        concrete_l2_r2_finite_combination_domain_witness_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2 finite-combination witness surface. -/
def concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessSurfaceReady

/-- Boundary theorem for the R2 finite-combination witness surface. -/
theorem concrete_analytic_spine_l2_r2_finite_combination_domain_witness_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteCombinationDomainWitnessHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_combination_domain_witness_surface_ready

end

end MathlibAnalytic
end MGAP4D
