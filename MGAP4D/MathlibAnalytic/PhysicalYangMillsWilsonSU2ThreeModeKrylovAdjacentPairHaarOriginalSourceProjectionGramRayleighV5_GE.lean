import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSourcePosteriorProjectionAutomaticIntegrabilityV5_GD
import Mathlib.Tactic

/-!
# P4-Q2-GE: put the GD source certificate into the ORIGINAL Wilson Gram

For any finite family f_i of ACTUAL gauge-invariant physical Hilbert inputs
and real coefficients a_i, FG already proves that the ORIGINAL physical
pair-Haar spatial-link Gram Rayleigh form equals the normalized true
Wilson conditional-response RMS energy of F := sum_i a_i f_i.

GD supplies a genuinely unconditional (for fixed beta>0) quantitative
lower certificate for the SAME source F, preserving:
- original interacting posterior, not an invented Haar conditional law;
- the exact signed FF receiver response, including drift;
- the actual physical transfer norm inverse squared;
- GA's concrete SU2 Wilson posterior Haar-variance coefficient.

Consequently the original Gram Rayleigh form dominates the integrated
source projection mass, for EVERY finite physical source family.
A separate theorem identifies the precise missing assumption for
a Rayleigh frame lower bound: an actual positive lower bound on that
physical source projection mass itself. This assumption is EXPLICIT,
not a claimed result. The original three-mode Krylov target is included
as a specialization.

No unproved source frame coercivity, spatial summability, H1-C3
strong-limit closure or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 550000

private noncomputable instance p4Q2GE_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Unconditional positive-beta lower certificate for the ORIGINAL
physical signed Wilson Gram Rayleigh on an arbitrary finite family.
The projection is evaluated on the actual combined signed physical
input F=∑aᵢfᵢ, not on separately orthogonalized artificial modes. -/
theorem p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  classical
  let F := ∑ i : ι, a i • f i
  let S := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hLower :=
    p4Q2GD_originalPhysicalPatchEnergy_ge_sourceProjection
      H beta hbeta F S
  have hPatch :=
    p4Q2FG_originalPhysicalRestrictedEnergy_eq_pairHaarConditionalRMSPatch
      H 2 (by norm_num) beta (le_of_lt hbeta) F S
  have hGram :=
    p4Q2FG_originalWilsonPhysicalGram_rayleigh_eq_pairHaarConditionalRMS
      H 2 (by norm_num) beta (le_of_lt hbeta) f a
  calc
    (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        ((Real.exp (-16 * beta) *
          (Real.exp (-32 * beta) *
            (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
            H beta (le_of_lt hbeta) F S) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy
        H 2 (by norm_num) beta (le_of_lt hbeta) F S := hLower
    _ = p4Q2FG_originalWilsonPairHaarConditionalRMSPatchEnergy
          H 2 (by norm_num) beta (le_of_lt hbeta) F S := hPatch
    _ = star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := hGram.symm

/-- The EXACT additional mathematical obligation for a physical
finite-mode uniform Gram floor is an actual lower frame bound
on the physical source projection mass. It is an explicit hypothesis,
not a consequence of posterior density separation alone. -/
theorem p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_of_sourceFrame
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ) (gamma : ℝ)
    (hFrame :
      gamma * (∑ i : ι, (a i) ^ 2) ≤
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        (gamma * (∑ i : ι, (a i) ^ 2))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) := by
  let C : ℝ := Real.exp (-16 * beta) *
    (Real.exp (-32 * beta) *
      (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))
  let L : ℝ := (1 / 2 : ℝ) *
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2
  have hC : 0 ≤ C :=
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (sq_nonneg _) 
          p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos.le))
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg _)
  have hScaled :
      L * (C * (gamma * (∑ i : ι, (a i) ^ 2))) ≤
      L * (C *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hFrame hC) hL
  calc
    (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        ((Real.exp (-16 * beta) *
          (Real.exp (-32 * beta) *
            (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
          (gamma * (∑ i : ι, (a i) ^ 2))) ≤
      L * (C *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : ι, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) := hScaled
    _ ≤ star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) :=
      p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
        H beta hbeta f a

/-- Direct three-mode specialization for the original SU(2) physical
right-Krylov receiver candidates. Their true physical nondegeneracy
has not been assumed or replaced by a synthetic basis. -/
theorem p4Q2GE_originalWilsonThreeModeGram_rayleigh_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : Fin 3 → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : Fin 3 → ℝ) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) (∑ i : Fin 3, a i • f i)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) ≤
      star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H 2 (by norm_num)
          beta (le_of_lt hbeta)
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver
            H 2 (by norm_num) beta (le_of_lt hbeta) (f i))) a) :=
  p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
    H beta hbeta f a

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_sourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GE_originalWilsonPhysicalGram_rayleigh_ge_of_sourceFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GE_originalWilsonThreeModeGram_rayleigh_ge_sourceProjection
