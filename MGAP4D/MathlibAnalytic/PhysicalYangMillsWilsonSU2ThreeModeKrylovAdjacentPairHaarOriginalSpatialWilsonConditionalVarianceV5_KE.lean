import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonKernelGramV5_KD
import Mathlib.Tactic

/-!
# P4-Q2-KE — exact genuine Wilson conditional mean and positive variance

The original one-slab Wilson kernel is normalized ONLY by its own
strictly positive spatial Haar mass at a fixed physical right boundary.
No interacting posterior is replaced, and no GI detector nonzero
witness is assumed. KD supplies the strictly positive genuine 2x2 Gram
determinant. We prove the exact mean/variance identities and the
strictly positive conditional variance at every finite volume and b.
We also characterize the vanishing centered first moment by equality
to the genuine conditional mean.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section Finite
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

/-- Genuine original Wilson conditional spatial mean at a fixed right boundary. -/
noncomputable def p4Q2KE_originalWilsonConditionalMean (b : ℝ) (B : Cfg) : ℝ :=
  p4Q2KB_originalSpatialWilsonActionKernelMoment H b B /
    p4Q2KB_originalSpatialWilsonKernelMass H b B

/-- Genuine original Wilson conditional spatial variance, from literal moments. -/
noncomputable def p4Q2KE_originalWilsonConditionalVariance (b : ℝ) (B : Cfg) : ℝ :=
  p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B /
      p4Q2KB_originalSpatialWilsonKernelMass H b B -
    (p4Q2KE_originalWilsonConditionalMean H b B) ^ 2

/-- The original Wilson centered first kernel moment vanishes exactly at
the genuine kernel conditional mean, not at an artificial posterior. -/
theorem p4Q2KE_originalWilsonCenteredFirstMoment_zero_iff
    (b : ℝ) (B : Cfg) (c : ℝ) :
    p4Q2KB_originalSpatialWilsonActionKernelMoment H b B -
      c * p4Q2KB_originalSpatialWilsonKernelMass H b B = 0 ↔
    c = p4Q2KE_originalWilsonConditionalMean H b B := by
  have hm0 := p4Q2KD_originalWilsonSpatialKernelMass_pos H b B
  unfold p4Q2KE_originalWilsonConditionalMean
  constructor
  · intro h
    have heq := sub_eq_zero.mp h
    apply (eq_div_iff (ne_of_gt hm0)).2
    simpa [mul_comm] using heq.symm
  · intro h
    have heq := (eq_div_iff (ne_of_gt hm0)).1 h
    apply sub_eq_zero.mpr
    simpa [mul_comm] using heq.symm

/-- Exact positive conditional variance identity from KD's actual
nondegenerate original Wilson spatial Gram matrix. -/
theorem p4Q2KE_originalWilsonConditionalVariance_eq_gram
    (b : ℝ) (B : Cfg) :
    p4Q2KE_originalWilsonConditionalVariance H b B =
      (p4Q2KB_originalSpatialWilsonKernelMass H b B *
          p4Q2KD_originalWilsonSpatialKernelSquareMoment H b B -
        (p4Q2KB_originalSpatialWilsonActionKernelMoment H b B) ^ 2) /
        (p4Q2KB_originalSpatialWilsonKernelMass H b B) ^ 2 := by
  have hm0 := (p4Q2KD_originalWilsonSpatialKernelMass_pos H b B).ne'
  unfold p4Q2KE_originalWilsonConditionalVariance
    p4Q2KE_originalWilsonConditionalMean
  field_simp
  ring

/-- Strictly positive genuine Wilson conditional spatial variance for
all real b and every physical right boundary, derived without a rank
assumption or a surrogate posterior. -/
theorem p4Q2KE_originalWilsonConditionalVariance_pos
    (b : ℝ) (B : Cfg) :
    0 < p4Q2KE_originalWilsonConditionalVariance H b B := by
  rw [p4Q2KE_originalWilsonConditionalVariance_eq_gram]
  exact div_pos
    (p4Q2KD_originalWilsonSpatialKernelGramDet_pos H b B)
    (sq_pos_of_pos (p4Q2KD_originalWilsonSpatialKernelMass_pos H b B))

/-- Centering at the genuine conditional mean leaves a strictly positive
original Wilson kernel energy, with no linear GI response claimed. -/
theorem p4Q2KE_originalWilsonCenteredAtMeanEnergy_pos
    (b : ℝ) (B : Cfg) :
    0 < ∫ A : Cfg,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b A B *
        (p4Q2JI_actualSpatialWilsonContinuous H A -
          p4Q2KE_originalWilsonConditionalMean H b B) ^ 2
      ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  exact p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos H b B
    (p4Q2KE_originalWilsonConditionalMean H b B)

end Finite
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KE_originalWilsonCenteredFirstMoment_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KE_originalWilsonConditionalVariance_eq_gram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KE_originalWilsonConditionalVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KE_originalWilsonCenteredAtMeanEnergy_pos
