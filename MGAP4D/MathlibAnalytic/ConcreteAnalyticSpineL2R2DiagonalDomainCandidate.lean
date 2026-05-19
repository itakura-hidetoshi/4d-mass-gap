import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R1HilbertCarrierClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R2 diagonal weight on the Mathlib completed real `ℓ²` carrier. -/
def concreteL2R2DiagonalWeight (n : ℕ) : ℝ :=
  (n : ℝ) + 1

/-- R2 weighted coordinate expression.  This is the coordinate formula for the
future diagonal operator; at this layer it is only a domain-candidate expression,
not yet a closed/self-adjoint operator. -/
def concreteL2R2WeightedCoordinate (x : ConcreteL2R1HilbertCarrier) (n : ℕ) : ℝ :=
  concreteL2R2DiagonalWeight n * x n

/-- R2 diagonal-domain candidate: vectors whose weighted coordinate square is
summable.  Density and closed-operator results are deliberately not claimed in
this candidate layer. -/
def ConcreteL2R2DiagonalDomainCandidate (x : ConcreteL2R1HilbertCarrier) : Prop :=
  Summable fun n : ℕ => (concreteL2R2WeightedCoordinate x n) ^ 2

/-- The zero vector belongs to the R2 diagonal-domain candidate.  This keeps the
candidate mathematically nonempty without yet claiming density. -/
theorem concrete_l2_r2_diagonal_domain_candidate_zero :
    ConcreteL2R2DiagonalDomainCandidate concreteL2R1HilbertZero := by
  unfold ConcreteL2R2DiagonalDomainCandidate concreteL2R2WeightedCoordinate
  refine (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr ?_
  intro n
  simp [concreteL2R1HilbertZero, lp.coeFn_zero]

/-- The raw diagonal action associated with the candidate domain.  Membership in
`ConcreteL2R2DiagonalDomainCandidate` is not required for merely writing the
coordinate formula; later layers will package it with domain membership. -/
def concreteL2R2DiagonalRawAction (x : ConcreteL2R1HilbertCarrier) : ℕ → ℝ :=
  fun n : ℕ => concreteL2R2WeightedCoordinate x n

/-- R2 domain-candidate surface.  This is the first R2 PR unit after the R1
Mathlib carrier closure. -/
structure ConcreteL2R2DiagonalDomainCandidateSurface where
  r1CarrierReady : concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady
  diagonalWeight : ℕ → ℝ
  weightedCoordinate : ConcreteL2R1HilbertCarrier → ℕ → ℝ
  domainCandidate : ConcreteL2R1HilbertCarrier → Prop
  zeroInDomainCandidate : domainCandidate concreteL2R1HilbertZero
  rawAction : ConcreteL2R1HilbertCarrier → ℕ → ℝ
  boundaryNotDenseDomainTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop

/-- Concrete R2 diagonal-domain candidate surface. -/
def concreteL2R2DiagonalDomainCandidateSurface :
    ConcreteL2R2DiagonalDomainCandidateSurface :=
  { r1CarrierReady :=
      concrete_analytic_spine_l2_r1_hilbert_carrier_closure_surface_ready
    diagonalWeight := concreteL2R2DiagonalWeight
    weightedCoordinate := concreteL2R2WeightedCoordinate
    domainCandidate := ConcreteL2R2DiagonalDomainCandidate
    zeroInDomainCandidate := concrete_l2_r2_diagonal_domain_candidate_zero
    rawAction := concreteL2R2DiagonalRawAction
    boundaryNotDenseDomainTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True }

/-- R2 diagonal-domain candidate readiness. -/
def concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady : Prop :=
  concreteAnalyticSpineL2R1HilbertCarrierClosureSurfaceReady ∧
  ConcreteL2R2DiagonalDomainCandidate concreteL2R1HilbertZero ∧
  concreteL2R2DiagonalDomainCandidateSurface.boundaryNotDenseDomainTheorem ∧
  concreteL2R2DiagonalDomainCandidateSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DiagonalDomainCandidateSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DiagonalDomainCandidateSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DiagonalDomainCandidateSurface.boundaryNotPVMConstruction

/-- R2 diagonal-domain candidate readiness theorem. -/
theorem concrete_analytic_spine_l2_r2_diagonal_domain_candidate_surface_ready :
    concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r1_hilbert_carrier_closure_surface_ready <|
      And.intro concrete_l2_r2_diagonal_domain_candidate_zero <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial trivial

/-- Boundary marker for the R2 diagonal-domain candidate surface. -/
def concreteAnalyticSpineL2R2DiagonalDomainCandidateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainCandidateSurfaceReady

/-- Boundary theorem for the R2 diagonal-domain candidate surface. -/
theorem concrete_analytic_spine_l2_r2_diagonal_domain_candidate_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DiagonalDomainCandidateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_diagonal_domain_candidate_surface_ready

end

end MathlibAnalytic
end MGAP4D
