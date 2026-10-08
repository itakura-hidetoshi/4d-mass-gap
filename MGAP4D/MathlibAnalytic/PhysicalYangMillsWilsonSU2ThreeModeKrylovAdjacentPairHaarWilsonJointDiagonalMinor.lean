import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarWilsonJointCrossingMinor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightCrossingGramStrict
import Mathlib.Tactic

/-!
# P4: concrete SU(2) diagonal two-boundary Wilson crossing minor

PR #5293 factored the original Wilson ground-state joint 2-by-2 crossing
minor into the physical transfer norm, four actual top-vacuum
representative values, and the literal temporal-gauge Wilson kernel minor.

Here we use an explicit *symmetric pair of boundary configurations*,
(A,A), (B,B) against (A,B), (B,A). The existing exact SU(2) temporal
crossing-kernel diagonal theorem gives crossing(A,A)=crossing(B,B)=1.
Its existing symmetry and the original one-slab half-weight sandwich
then identify the TRUE crossing minor as

  halfWeight(A)^2 * halfWeight(B)^2 * (1 - crossing(A,B)^2).

Both half-weights and the original crossing kernel are strictly positive.
Consequently a strictly subunit OFF-DIAGONAL temporal crossing-kernel
value forces a strictly POSITIVE actual Wilson crossing minor. When the
actual physical top vacuum is also nonzero at A and B, the original
normalized physical joint density has a strictly positive crossing
minor and cannot be pointwise separated across its two boundaries.

The remaining model-specific obstruction is **constructing A, B
with crossing(A,B)<1 for the desired positive-beta physical
finite volumes**, and the independent a.e. linkage needed for a
strict posterior-fiber energy statement. Neither is asserted here.
No Dobrushin, surrogate law, volume-uniform estimate or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4SU2DiagCrossTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4SU2DiagCrossCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4SU2DiagCrossSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4SU2DiagCrossMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4SU2DiagCrossBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4SU2DiagCrossLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine full one-slab Wilson kernel 2x2 determinant in
the symmetric two-boundary configuration has an EXACT half-weight
square factor and a single off-diagonal temporal crossing defect. -/
theorem originalWilsonTemporalKernelTwoByTwoMinor_symmetric_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    originalWilsonTemporalKernelTwoByTwoMinor H 2 beta A B A B =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 beta A ^ 2 *
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 beta B ^ 2 *
      (1 - periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 beta A B ^ 2) := by
  unfold originalWilsonTemporalKernelTwoByTwoMinor
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  rw [periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_self H beta A,
      periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_self H beta B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
        H 2 (by norm_num) beta hbeta B A]
  ring

/-- Concrete criterion: off-diagonal temporal crossing strictly below
one forces a STRICTLY POSITIVE full Wilson one-slab kernel determinant,
without any top-vacuum or posterior approximation. -/
theorem originalWilsonTemporalKernelTwoByTwoMinor_pos_of_crossing_lt_one_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hstrict : periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta A B < 1) :
    0 < originalWilsonTemporalKernelTwoByTwoMinor H 2 beta A B A B := by
  have hcross : 0 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 beta A B :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_pos
      H 2 beta A B).le
  have hdef : 0 <
      1 - periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 beta A B ^ 2 := by
    nlinarith
  rw [originalWilsonTemporalKernelTwoByTwoMinor_symmetric_SU2
    H beta hbeta A B]
  exact mul_pos
    (mul_pos
      (pow_pos (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
        H 2 beta A) 2)
      (pow_pos (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
        H 2 beta B) 2))
    hdef

/-- When the four original physical top-vacuum values are nonzero
(here only the two values Omega(A), Omega(B)), the actual normalized
Wilson ground-state joint density inherits the STRICTLY POSITIVE
crossing minor. No pointwise claim is made outside these inputs. -/
theorem originalWilsonJointTwoByTwoMinor_symmetric_pos_of_crossing_lt_one_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hA : 0 < originalWilsonPhysicalTopVacuumValue
      H 2 (by norm_num) beta hbeta A)
    (hB : 0 < originalWilsonPhysicalTopVacuumValue
      H 2 (by norm_num) beta hbeta B)
    (hstrict : periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta A B < 1) :
    0 < originalWilsonJointTwoByTwoMinor
      H 2 (by norm_num) beta hbeta A B A B := by
  have hK : 0 < originalWilsonTemporalKernelTwoByTwoMinor
      H 2 beta A B A B :=
    originalWilsonTemporalKernelTwoByTwoMinor_pos_of_crossing_lt_one_SU2
      H beta hbeta A B hstrict
  have hTpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta hbeta
  rw [originalWilsonJointTwoByTwoMinor_eq_vacuumFactors_mul_temporalKernelMinor]
  exact mul_pos
    (mul_pos
      (pow_pos (inv_pos.mpr hTpos) 2)
      (mul_pos (mul_pos (mul_pos hA hB) hA) hB))
    hK

/-- Under the explicit off-diagonal strictness and nonzero
physical-vacuum witness hypotheses, the ORIGINAL normalized Wilson
joint density is not a pointwise rank-one boundary product. -/
theorem originalWilsonJointNormalizedWeight_not_pointwise_separable_of_crossing_lt_one_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hA : 0 < originalWilsonPhysicalTopVacuumValue
      H 2 (by norm_num) beta hbeta A)
    (hB : 0 < originalWilsonPhysicalTopVacuumValue
      H 2 (by norm_num) beta hbeta B)
    (hstrict : periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta A B < 1) :
    ¬ ∃ (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ),
      ∀ X Y,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta (X, Y) = F X * G Y := by
  have hminor :=
    originalWilsonJointTwoByTwoMinor_symmetric_pos_of_crossing_lt_one_SU2
      H beta hbeta A B hA hB hstrict
  intro ⟨F, G, hsep⟩
  have hzero : originalWilsonJointTwoByTwoMinor
      H 2 (by norm_num) beta hbeta A B A B = 0 := by
    unfold originalWilsonJointTwoByTwoMinor
    rw [hsep A A, hsep B B, hsep A B, hsep B A]
    ring
  exact (ne_of_gt hminor) hzero

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
