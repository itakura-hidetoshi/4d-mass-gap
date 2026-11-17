import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaussHilbertInfiniteExcitationV5_PZ37AMU
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMV — genuinely nontrivial normalized physical Wilson one-slab

AMU constructs a unit vector in the original finite-volume SU(2) physical
Gauss-law Hilbert space orthogonal to the complete normalized Wilson
one-slab top eigenspace. The existing strict finite-volume operator-norm
bound applies to this explicit nonzero physical sector. The current stage
proves, without an extra witness or strictness hypothesis, that the
normalized genuine physical Wilson one-slab does not fix this vector
and therefore is not the identity operator.

This is a statement about the genuine physical Wilson operator, NOT the
abstract identity OS semigroup of AMR, and NOT an OS–Wilson identification.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMV_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- An actual normalized finite-volume SU(2) Wilson one-slab maps a unit
physical Gauss-law state in the complete top-eigenspace orthogonal complement
to a vector of strictly smaller norm. This is not an abstract sector model. -/
theorem p4Q2PZ37AMV_exists_originalPhysical_unit_strict_oneSlab_contraction
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ u : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2,
      ‖u‖ = 1 ∧
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta u‖ < 1 := by
  have hTwo : 0 < (2 : ℕ) := by norm_num
  obtain ⟨u, huNorm, huOrth⟩ :=
    p4Q2PZ37AMU_exists_originalPhysical_unitTopOrthogonalExcitation H beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 hTwo beta hbeta
  let w : K := ⟨u, huOrth⟩
  let R : K →L[ℝ] K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H 2 hTwo beta hbeta
  let S : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 hTwo beta hbeta
  have hwNorm : ‖w‖ = 1 := by
    change ‖u‖ = 1
    exact huNorm
  -- The generic certified power-apply bound retains the ambient Hilbert
  -- NormedSpace instance; direct R.le_opNorm fails to reconstruct the
  -- bundled submodule NormedSpace on this pinned Mathlib version.
  have hS :
      (S : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2).IsSymmetric := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H 2 hTwo beta hbeta
  have hRBound : ‖R w‖ ≤ ‖R‖ * ‖w‖ := by
    have hApply :=
      realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le S hS 1 w
    change
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS w‖ ≤
        ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ * ‖w‖
    simpa only [pow_one] using hApply
  have hRStrict : ‖R‖ < 1 := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 hTwo beta hbeta
  have hCoe : ‖S u‖ = ‖R w‖ := by
    rfl
  refine ⟨u, huNorm, ?_⟩
  change ‖S u‖ < 1
  calc
    ‖S u‖ = ‖R w‖ := hCoe
    _ ≤ ‖R‖ * ‖w‖ := hRBound
    _ = ‖R‖ := by rw [hwNorm, mul_one]
    _ < 1 := hRStrict

/-- The same original physical Gauss-law state is genuinely moved by the
normalized finite-volume Wilson one-slab operator. -/
theorem p4Q2PZ37AMV_exists_originalPhysical_unit_nonfixed_oneSlab
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ u : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2,
      ‖u‖ = 1 ∧
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta u ≠ u := by
  obtain ⟨u, hu, hStrict⟩ :=
    p4Q2PZ37AMV_exists_originalPhysical_unit_strict_oneSlab_contraction H beta hbeta
  refine ⟨u, hu, ?_⟩
  intro hFixed
  rw [hFixed, hu] at hStrict
  exact (lt_irrefl (1 : ℝ)) hStrict

/-- Consequently the ORIGINAL normalized SU(2) physical Wilson one-slab
operator itself is not the identity. Neither the abstract OS family
C.translate nor a completed OS boundary operator appears in the statement. -/
theorem p4Q2PZ37AMV_originalPhysical_normalized_oneSlab_ne_identity
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta ≠
      ContinuousLinearMap.id ℝ
        (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) := by
  obtain ⟨u, _, hu⟩ :=
    p4Q2PZ37AMV_exists_originalPhysical_unit_nonfixed_oneSlab H beta hbeta
  intro hIdentity
  apply hu
  rw [hIdentity]
  simp

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMV_exists_originalPhysical_unit_strict_oneSlab_contraction
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMV_exists_originalPhysical_unit_nonfixed_oneSlab
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMV_originalPhysical_normalized_oneSlab_ne_identity
