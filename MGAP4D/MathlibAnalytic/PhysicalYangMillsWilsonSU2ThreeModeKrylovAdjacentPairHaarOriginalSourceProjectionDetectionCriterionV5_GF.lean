import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSourceProjectionGramRayleighV5_GE
import Mathlib.Tactic

/-!
# P4-Q2-GF: true-Wilson projected-source detection and Gram obstruction

The exact GF interface takes GE's genuine original finite-volume physical
Gram Rayleigh lower certificate and makes its source-dependent logical
consequences explicit, without inventing a positive frame constant.

At each fixed beta>0 the fully physical coefficient

 (1/2) * ||T_beta||^(-2) * exp(-16 beta) *
      exp(-32 beta) * beta^2 * V_SU2

is strictly positive, using the already established original Wilson
physical transfer norm positivity and original SU(2) Haar variance.

For every actual finite physical source family, a strictly positive
pair-Haar sum of squared true-Wilson source/contrast projections IMPLIES
strictly positive ORIGINAL physical Gram Rayleigh. Conversely if the
original physical Gram Rayleigh vanishes, the source/contrast projected
mass is zero. This locates the potential obstruction in an actual physical
source, rather than an assumed coefficient-space frame.

There is also a direct three-mode right-Krylov criterion. It requires
actual source detection for each nonzero physical linear combination;
we do NOT assert that requirement without proof.

No independent posterior, Dobrushin, source frame assumption hidden as
a fact, continuum uniform gap, or H1-C3 closure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 600000

private noncomputable instance p4Q2GF_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Original physical transfer normalization remains strictly positive
at fixed positive Wilson beta: its norm is the ORIGINAL transfer norm,
not an artificially set-to-one normalization. -/
theorem p4Q2GF_originalWilsonSourceProjectionGramScale_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 <
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      (Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) := by
  have hT : 0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta (le_of_lt hbeta)
  exact mul_pos
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (pow_pos (inv_pos.mpr hT) 2))
    (mul_pos (Real.exp_pos _)
      (mul_pos (Real.exp_pos _)
        (mul_pos (pow_pos hbeta 2)
          p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos))

/-- Physical projected source mass is nonnegative at each genuine
spatial link because it is the outer pair-Haar integral of a real square. -/
theorem p4Q2GF_originalWilsonSourceProjectedLinkMean_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
      H beta hbeta f e := by
  unfold p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
  exact integral_nonneg (fun z => sq_nonneg _)

/-- Every actual finite-link source/contrast projected mass is nonnegative.
This is an authentic source-dependent certificate, not a frame assumption. -/
theorem p4Q2GF_originalWilsonSourceProjectedSpatialMass_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
      H beta hbeta f S := by
  classical
  unfold p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
  exact Finset.sum_nonneg (fun e _ =>
    p4Q2GF_originalWilsonSourceProjectedLinkMean_nonneg
      H beta hbeta f e)

/-- Vanishing physical projected mass on an arbitrary real link patch
is EQUIVALENT to vanishing of every original integrated link projection.
No falsely strengthened nonzero source assumption is used. -/
theorem p4Q2GF_originalWilsonProjectedPatch_zero_iff_allLinks_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
      H beta hbeta f S = 0 ↔
        ∀ e ∈ S,
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
            H beta hbeta f e = 0 := by
  classical
  unfold p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
  exact Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
    p4Q2GF_originalWilsonSourceProjectedLinkMean_nonneg H beta hbeta f e)

/-- The original Wilson finite physical Gram Rayleigh is STRICTLY
POSITIVE whenever its actual combined signed physical source has a
strictly positive right posterior-contrast projected mass. -/
theorem p4Q2GF_originalWilsonPhysicalGram_pos_of_projectedSource_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (hDetect :
      0 < p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 (by norm_num) beta (le_of_lt hbeta)
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  have hScale := p4Q2GF_originalWilsonSourceProjectionGramScale_pos
    H beta hbeta
  have hLower :=
    p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
      H beta hbeta f a
  have hPos : 0 <
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) := by
    calc
      (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        ((Real.exp (-16 * beta) *
          (Real.exp (-32 * beta) *
            (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
            H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
            (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) =
        ((1 / 2 : ℝ) *
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
          (Real.exp (-16 * beta) *
            (Real.exp (-32 * beta) *
              (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)))) *
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
            H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
            (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
              ring
      _ > 0 := mul_pos hScale hDetect
  exact lt_of_lt_of_le hPos hLower

/-- If an ORIGINAL Wilson Gram Rayleigh degenerates, then the source's
pair-Haar posterior-contrast projected mass vanishes. This is a
necessary obstruction, not an unproved equivalence. -/
theorem p4Q2GF_originalWilsonGram_zero_implies_projectedSource_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ)
    (hZero :
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num) beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) = 0) :
    p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
      H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) = 0 := by
  let Q := p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
    H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hQNonneg : 0 ≤ Q :=
    p4Q2GF_originalWilsonSourceProjectedSpatialMass_nonneg
      H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  by_contra hQzero
  have hQPos : 0 < Q := lt_of_le_of_ne hQNonneg (Ne.symm hQzero)
  have hRayPos :=
    p4Q2GF_originalWilsonPhysicalGram_pos_of_projectedSource_pos
      H beta hbeta f a hQPos
  exact (ne_of_gt hRayPos) hZero

/-- Direct three-mode physical right-Krylov detection criterion, applied
to ACTUAL source combinations. The injective detection premise is
explicit and awaits a genuine Wilson receiver witness theorem. -/
theorem p4Q2GF_originalWilsonThreeModeGram_strict_of_sourceDetection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : Fin 3 → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hDetect : ∀ (a : Fin 3 → ℝ), a ≠ 0 →
      0 < p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) (∑ i : Fin 3, a i • f i)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :
    ∀ (a : Fin 3 → ℝ), a ≠ 0 →
      0 < star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  intro a ha
  exact p4Q2GF_originalWilsonPhysicalGram_pos_of_projectedSource_pos
    H beta hbeta f a (hDetect a ha)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonSourceProjectionGramScale_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonSourceProjectedLinkMean_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonSourceProjectedSpatialMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonProjectedPatch_zero_iff_allLinks_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonPhysicalGram_pos_of_projectedSource_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonGram_zero_implies_projectedSource_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GF_originalWilsonThreeModeGram_strict_of_sourceDetection
