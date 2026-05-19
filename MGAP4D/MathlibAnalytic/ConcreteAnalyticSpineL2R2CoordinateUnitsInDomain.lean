import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalDomainCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Each Mathlib coordinate unit belongs to the R2 diagonal-domain candidate.
This is the first nonzero domain-membership theorem for the R2 diagonal lane.
It uses the one-point support of `lp.single` via `hasSum_single`, and does not
claim density, closedness, self-adjointness, or spectral data. -/
theorem concrete_l2_r2_diagonal_domain_candidate_mathlib_unit (k : ℕ) :
    ConcreteL2R2DiagonalDomainCandidate (concreteL2MathlibUnit k) := by
  unfold ConcreteL2R2DiagonalDomainCandidate
  have hs :
      HasSum
        (fun n : ℕ => (concreteL2R2WeightedCoordinate (concreteL2MathlibUnit k) n) ^ 2)
        ((concreteL2R2WeightedCoordinate (concreteL2MathlibUnit k) k) ^ 2) := by
    refine hasSum_single k ?_
    intro n hn
    simp [concreteL2R2WeightedCoordinate, concrete_l2_mathlib_unit_apply_ne hn]
  exact hs.summable

/-- R2 coordinate-unit domain-membership adapter. -/
def concreteL2R2CoordinateUnitDomainMembershipAdapter : Prop :=
  ∀ k : ℕ, ConcreteL2R2DiagonalDomainCandidate (concreteL2MathlibUnit k)

/-- Adapter theorem for coordinate-unit domain membership. -/
theorem concrete_l2_r2_coordinate_unit_domain_membership_adapter_ready :
    concreteL2R2CoordinateUnitDomainMembershipAdapter := by
  exact concrete_l2_r2_diagonal_domain_candidate_mathlib_unit

/-- R2 coordinate-unit domain-membership surface.  It upgrades the previous
nonempty domain candidate by adding all Mathlib coordinate units, while keeping
all stronger operator-theoretic obligations out of scope. -/
structure ConcreteL2R2CoordinateUnitsInDomainSurface where
  r2DomainCandidateReady : concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady
  coordinateUnitDomainLaw :
    ∀ k : ℕ, ConcreteL2R2DiagonalDomainCandidate (concreteL2MathlibUnit k)
  boundaryNotFiniteLinearCombinationDomainTheorem : Prop
  boundaryNotDenseDomainTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop

/-- Concrete R2 coordinate-unit domain-membership surface. -/
def concreteL2R2CoordinateUnitsInDomainSurface :
    ConcreteL2R2CoordinateUnitsInDomainSurface :=
  { r2DomainCandidateReady :=
      concrete_analytic_spine_l2_r2_diagonal_domain_candidate_surface_ready
    coordinateUnitDomainLaw := concrete_l2_r2_diagonal_domain_candidate_mathlib_unit
    boundaryNotFiniteLinearCombinationDomainTheorem := True
    boundaryNotDenseDomainTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True }

/-- R2 coordinate-unit domain-membership readiness. -/
def concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady ∧
  concreteL2R2CoordinateUnitDomainMembershipAdapter ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotFiniteLinearCombinationDomainTheorem ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotDenseDomainTheorem ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2CoordinateUnitsInDomainSurface.boundaryNotPVMConstruction

/-- R2 coordinate-unit domain-membership readiness theorem. -/
theorem concrete_analytic_spine_l2_r2_coordinate_units_in_domain_surface_ready :
    concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady := by
  unfold concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_domain_candidate_surface_ready <|
      And.intro concrete_l2_r2_coordinate_unit_domain_membership_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2 coordinate-unit domain-membership surface. -/
def concreteAnalyticSpineL2R2CoordinateUnitsInDomainHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2CoordinateUnitsInDomainSurfaceReady

/-- Boundary theorem for the R2 coordinate-unit domain-membership surface. -/
theorem concrete_analytic_spine_l2_r2_coordinate_units_in_domain_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2CoordinateUnitsInDomainHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_coordinate_units_in_domain_surface_ready

end

end MathlibAnalytic
end MGAP4D
