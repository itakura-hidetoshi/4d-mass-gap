import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateUnitsInDomain

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite coordinate combinations in the Mathlib completed real `ℓ²` carrier.
This packages the algebraic span of the coordinate units without yet claiming
that this span is dense in the graph norm or that it is an operator core. -/
def concreteL2R2FiniteCoordinateCombination (s : Finset ℕ) (a : ℕ → ℝ) :
    ConcreteL2R1HilbertCarrier :=
  s.sum (fun k => a k • (concreteL2MathlibUnit k : ConcreteL2R1HilbertCarrier))

/-- A finite coordinate combination vanishes outside its finite index set. -/
theorem concrete_l2_r2_finite_coordinate_combination_apply_of_not_mem
    (s : Finset ℕ) (a : ℕ → ℝ) {n : ℕ} (hn : n ∉ s) :
    concreteL2R2FiniteCoordinateCombination s a n = 0 := by
  classical
  unfold concreteL2R2FiniteCoordinateCombination
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hnk : n ≠ k := by
    intro h
    exact hn (by simpa [h] using hk)
  simp [concrete_l2_mathlib_unit_apply_ne hnk]

/-- The weighted-square sequence of a finite coordinate combination has finite
support.  This is the finite-support bridge used to avoid any premature density
or closed-operator claim. -/
theorem concrete_l2_r2_finite_coordinate_combination_weighted_square_has_finite_support
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Function.HasFiniteSupport fun n : ℕ =>
      (concreteL2R2WeightedCoordinate
        (concreteL2R2FiniteCoordinateCombination s a) n) ^ 2 := by
  unfold Function.HasFiniteSupport
  refine s.finite_toSet.subset ?_
  intro n hn
  by_contra hns
  have hz :
      (concreteL2R2WeightedCoordinate
        (concreteL2R2FiniteCoordinateCombination s a) n) ^ 2 = 0 := by
    simp [concreteL2R2WeightedCoordinate,
      concrete_l2_r2_finite_coordinate_combination_apply_of_not_mem s a hns]
  exact hn hz

/-- Every finite coordinate combination belongs to the R2 diagonal-domain
candidate.  The proof is finite-support based: the weighted-square sequence is
zero off the finite index set, hence summable. -/
theorem concrete_l2_r2_diagonal_domain_candidate_finite_coordinate_combination
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ConcreteL2R2DiagonalDomainCandidate
      (concreteL2R2FiniteCoordinateCombination s a) := by
  unfold ConcreteL2R2DiagonalDomainCandidate
  exact summable_of_hasFiniteSupport
    (concrete_l2_r2_finite_coordinate_combination_weighted_square_has_finite_support s a)

/-- R2 finite-coordinate-combination domain-membership adapter. -/
def concreteL2R2FiniteCoordinateCombinationDomainMembershipAdapter : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → ℝ),
    ConcreteL2R2DiagonalDomainCandidate
      (concreteL2R2FiniteCoordinateCombination s a)

/-- Adapter theorem for R2 finite-coordinate-combination domain membership. -/
theorem concrete_l2_r2_finite_coordinate_combination_domain_membership_adapter_ready :
    concreteL2R2FiniteCoordinateCombinationDomainMembershipAdapter := by
  exact concrete_l2_r2_diagonal_domain_candidate_finite_coordinate_combination

/-- R2 finite-coordinate-combination domain-membership surface.  This is the
algebraic-span PR unit: it proves that finite sums of coordinate units are inside
the candidate domain, while preserving the stronger boundaries for density,
operator-core, closedness, self-adjointness, and spectral/PVM construction. -/
structure ConcreteL2R2FiniteCoordinateCombinationsInDomainSurface where
  coordinateUnitsInDomainReady :
    concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady
  finiteCoordinateCombination : Finset ℕ → (ℕ → ℝ) → ConcreteL2R1HilbertCarrier
  finiteCombinationDomainLaw :
    ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      ConcreteL2R2DiagonalDomainCandidate (finiteCoordinateCombination s a)
  boundaryNotDenseDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop

/-- Concrete R2 finite-coordinate-combination domain-membership surface. -/
def concreteL2R2FiniteCoordinateCombinationsInDomainSurface :
    ConcreteL2R2FiniteCoordinateCombinationsInDomainSurface :=
  { coordinateUnitsInDomainReady :=
      concrete_analytic_spine_l2_r2_coordinate_units_in_domain_surface_ready
    finiteCoordinateCombination := concreteL2R2FiniteCoordinateCombination
    finiteCombinationDomainLaw :=
      concrete_l2_r2_diagonal_domain_candidate_finite_coordinate_combination
    boundaryNotDenseDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True }

/-- R2 finite-coordinate-combination domain-membership readiness. -/
def concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady ∧
  concreteL2R2FiniteCoordinateCombinationDomainMembershipAdapter ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotDenseDomainTheorem ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteCoordinateCombinationsInDomainSurface.boundaryNotPVMConstruction

/-- R2 finite-coordinate-combination domain-membership readiness theorem. -/
theorem concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready :
    concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_coordinate_units_in_domain_surface_ready <|
      And.intro
        concrete_l2_r2_finite_coordinate_combination_domain_membership_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2 finite-coordinate-combination domain surface. -/
def concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady

/-- Boundary theorem for the R2 finite-coordinate-combination domain surface. -/
theorem concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready

end

end MathlibAnalytic
end MGAP4D
