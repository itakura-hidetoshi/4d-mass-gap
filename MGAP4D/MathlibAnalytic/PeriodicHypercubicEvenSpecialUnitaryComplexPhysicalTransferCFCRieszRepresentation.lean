import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszRadiusIndependence

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology Metric
open scoped InnerProductSpace InnerProduct Ring Topology Interval Real

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszRepresentationCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The normalized resolvent contour projector at a chosen circle radius around
the isolated transfer eigenvalue `1`.  Admissibility of the radius is kept out
of the definition and enters only in the representation theorems below. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (r : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    (∮ z in C((1 : ℂ), r),
      resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) z)

/-- Every admissible circle represents exactly the isolated-top CFC projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection_of_radius_lt_gap
      H N hN beta hbeta r hr hrgap

/-- Hence every admissible Riesz contour is Mathlib's canonical orthogonal
projection onto the full complex eigenvalue-one space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_topSpectralProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]

/-- The same admissible Riesz contour is exactly the scalar extension of the
genuine real physical top spectral projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_complexification
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification]

/-- The range of every admissible Riesz contour projector is the entire complex
top eigenspace, with no simplicity or rank-one hypothesis. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_range
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
      H N hN beta hbeta r).range =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
        H N hN beta hbeta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range
      H N hN beta hbeta

/-- Every admissible normalized Riesz contour integral is a genuine orthogonal
star projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_isStarProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    IsStarProjection
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_isStarProjection
      H N hN beta hbeta

/-- The operator-valued Riesz projector itself is independent of the chosen
admissible radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_of_admissible
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr₁gap :
      r₁ < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (hr₂gap :
      r₂ < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r₁ =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r₂ := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_radius_independent
      H N hN beta hbeta r₁ r₂ hr₁ hr₂ hr₁gap hr₂gap

/-- Audit-visible unification of the contour, CFC, complex spectral, and real
physical presentations of the isolated top projector. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszRepresentationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  rieszEqualsCFC :
    ∀ r : ℝ,
      0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta
  rieszEqualsComplexSpectral :
    ∀ r : ℝ,
      0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta
  rieszEqualsRealComplexification :
    ∀ r : ℝ,
      0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r =
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
            H N hN beta hbeta)
  rieszRange :
    ∀ r : ℝ,
      0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
        H N hN beta hbeta r).range =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta
  rieszStarProjection :
    ∀ r : ℝ,
      0 < r →
      r < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      IsStarProjection
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r)
  radiusIndependent :
    ∀ r₁ r₂ : ℝ,
      0 < r₁ →
      0 < r₂ →
      r₁ < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      r₂ < 1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ →
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r₁ =
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius
          H N hN beta hbeta r₂

/-- Construct the representation-independent isolated-top Riesz package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszRepresentationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszRepresentationPackage
      H N hN beta hbeta :=
  { rieszEqualsCFC :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
        H N hN beta hbeta
    rieszEqualsComplexSpectral :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_topSpectralProjection
        H N hN beta hbeta
    rieszEqualsRealComplexification :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_complexification
        H N hN beta hbeta
    rieszRange :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_range
        H N hN beta hbeta
    rieszStarProjection :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_isStarProjection
        H N hN beta hbeta
    radiusIndependent :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_of_admissible
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
