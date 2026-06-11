import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Boundary record for the current role of `exactGapValueReal`.

The value `exactGapValueReal` is the public projection of the concrete
Hamiltonian/PVM/spectral package.  This boundary carries provenance and order
facts only; it does not install a separate upstream closed-form equality theorem
for the carrier. -/
structure ExactGapValueDerivationBoundary where
  normalizedCarrierPositive : 0 < exactGapValueReal
  normalizedCarrierAboveOne : 1 < exactGapValueReal
  normalizedCarrierIsHamiltonianProjection :
    exactGapValueReal = hamiltonianPVMSpectralExactGapValue
  theoremRouteCertified : exactGapRealSurface.certified
  pvmWindowMembership :
    exactGapValueReal ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow
  spectralSupportMembership :
    exactGapValueReal ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport
  spectralSupportLowerBound :
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport →
        exactGapValueReal ≤ x
  pvmWindowLowerBound :
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow →
        exactGapValueReal ≤ x
  positiveSpectralWeight :
    0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow
  nonzeroSpectralWeight :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0

/-- Certification predicate for the exact-value derivation boundary. -/
def ExactGapValueDerivationBoundary.certified
    (B : ExactGapValueDerivationBoundary) : Prop :=
  0 < exactGapValueReal ∧
  1 < exactGapValueReal ∧
  exactGapValueReal = hamiltonianPVMSpectralExactGapValue ∧
  exactGapRealSurface.certified ∧
  exactGapValueReal ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ∧
  exactGapValueReal ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport ∧
  (∀ x : ℝ,
    x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport →
      exactGapValueReal ≤ x) ∧
  (∀ x : ℝ,
    x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow →
      exactGapValueReal ≤ x) ∧
  0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
    concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ∧
  concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
    concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0

/-- Backward-compatible readiness name during downstream migration. -/
def ExactGapValueDerivationBoundary.ready
    (B : ExactGapValueDerivationBoundary) : Prop :=
  B.certified

/-- Canonical boundary for the current normalized exact-gap carrier. -/
def exactGapValueDerivationBoundary : ExactGapValueDerivationBoundary :=
  { normalizedCarrierPositive := exactGapValueReal_pos
    normalizedCarrierAboveOne := exactGapRealSurface.above_one
    normalizedCarrierIsHamiltonianProjection := rfl
    theoremRouteCertified := exact_gap_real_surface_certified
    pvmWindowMembership := exactGapRealSurface.pvmWindowMembership
    spectralSupportMembership := exactGapRealSurface.spectralSupportMembership
    spectralSupportLowerBound := exactGapRealSurface.spectralSupportLowerBound
    pvmWindowLowerBound := exactGapRealSurface.pvmWindowLowerBound
    positiveSpectralWeight := exactGapRealSurface.positiveSpectralWeight
    nonzeroSpectralWeight := exactGapRealSurface.nonzeroSpectralWeight }

/-- The current exact-value boundary is certified. -/
theorem exact_gap_value_derivation_boundary_certified :
    exactGapValueDerivationBoundary.certified := by
  exact ⟨
    exactGapValueDerivationBoundary.normalizedCarrierPositive,
    exactGapValueDerivationBoundary.normalizedCarrierAboveOne,
    exactGapValueDerivationBoundary.normalizedCarrierIsHamiltonianProjection,
    exactGapValueDerivationBoundary.theoremRouteCertified,
    exactGapValueDerivationBoundary.pvmWindowMembership,
    exactGapValueDerivationBoundary.spectralSupportMembership,
    exactGapValueDerivationBoundary.spectralSupportLowerBound,
    exactGapValueDerivationBoundary.pvmWindowLowerBound,
    exactGapValueDerivationBoundary.positiveSpectralWeight,
    exactGapValueDerivationBoundary.nonzeroSpectralWeight⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem exact_gap_value_derivation_boundary_ready :
    exactGapValueDerivationBoundary.ready := by
  exact exact_gap_value_derivation_boundary_certified

/-- The positivity of the normalized carrier is certified by the provenance route. -/
theorem exact_gap_value_real_normalized_seed_positive :
    0 < exactGapValueReal := by
  exact exactGapValueDerivationBoundary.normalizedCarrierPositive

/-- The normalized carrier is above one through the provenance route. -/
theorem exact_gap_value_real_normalized_seed_above_one :
    1 < exactGapValueReal := by
  exact exactGapValueDerivationBoundary.normalizedCarrierAboveOne

/-- The public carrier is the projection of the Hamiltonian/PVM/spectral package. -/
theorem exact_gap_value_hamiltonian_projection_identity :
    exactGapValueReal = hamiltonianPVMSpectralExactGapValue := by
  exact exactGapValueDerivationBoundary.normalizedCarrierIsHamiltonianProjection

/-- The Hamiltonian/PVM/spectral route is certified at the boundary. -/
theorem exact_gap_value_theorem_route_certified :
    exactGapRealSurface.certified := by
  exact exactGapValueDerivationBoundary.theoremRouteCertified

/-- The boundary carries the concrete positive spectral-weight fact. -/
theorem exact_gap_value_positive_spectral_weight_boundary :
    0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow := by
  exact exactGapValueDerivationBoundary.positiveSpectralWeight

/-- The boundary carries the concrete nonzero spectral-weight fact. -/
theorem exact_gap_value_nonzero_spectral_weight_boundary :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0 := by
  exact exactGapValueDerivationBoundary.nonzeroSpectralWeight

end MathlibAnalytic
end MGAP4D