import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRegularizedFrozenRightLinkCandidate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkWeightHarnack
import Mathlib.Tactic

/-!
# P4-Q1: original canonical Wilson joint density has a local, volume-independent Harnack ratio

P4-Q1 cannot turn the strict fixed-volume posterior vacuum energy
from P4-F3 into a volume-uniform quantitative bound by fiat.
The actual canonical Wilson joint density has, however, a
pointwise Harnack comparison under replacement of ONE right link.
The existing physical vacuum Harnack factor is exp(8 beta), and
the literal Wilson kernel Harnack factor is exp(8 beta). Their
product gives exp(16 beta), INDEPENDENT of spatial extent H.

This file transports that existing one-link result to the ACTUAL
continuous representative W_c of the original physical normalized
Wilson joint law (PR #5296), and in particular to the right-link
identity-frozen configuration used by the explicit P4-Q1 candidates
(PR #5303). The original normalized Wilson density is equal to
W_c only a.e. under pair Haar; no unjustified equality of arbitrary
L2 representative values is asserted. There is no change to the
underlying physical joint law.

These are pointwise physical-density estimates, not an as-yet
unproved uniform sum of posterior L2 errors. No Dobrushin, new
posterior, sorry/admit, or continuum mass-gap claim is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q1HarnackTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1HarnackCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1HarnackSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1HarnackMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1HarnackBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1HarnackSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ACTUAL canonical continuous normalized Wilson joint density
is everywhere positive, not merely Haar-almost everywhere positive
like an arbitrary representative of the original L2 top vacuum. -/
theorem originalWilsonContinuousPhysicalJointWeight_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < originalWilsonContinuousPhysicalJointWeight H beta hbeta z := by
  have hlambda :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta hbeta
  have hA :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta z.1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) beta hbeta z.1
  have hB :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta z.2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) beta hbeta z.2
  have hK :
      0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta z.1 z.2 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 beta z.1 z.2
  unfold originalWilsonContinuousPhysicalJointWeight
  exact mul_pos (mul_pos (mul_pos (inv_pos.mpr hlambda) hA) hK) hB

/-- Exact original canonical continuous physical Wilson joint:
ONE right-link replacement has the volume-independent real Harnack
factor exp(16 beta). The left boundary is kept literally fixed. -/
theorem originalWilsonContinuousPhysicalJointWeight_rightLink_le_exp_sixteen_mul
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (A, Function.update B e g) ≤
      Real.exp (16 * beta) *
        originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (A, Function.update B e h) := by
  simpa only [originalWilsonContinuousPhysicalJointWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal,
    mul_assoc] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_update_right_le_exp_sixteen_mul_update_right
      H 2 (by norm_num) beta hbeta A B e g h)

/-- The actual original W_c at (A,B) and at (A,B[e<-1]) are
comparable with the SAME volume-independent Harnack factor. -/
theorem originalWilsonContinuousPhysicalJointWeight_le_exp_sixteen_mul_frozen
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    originalWilsonContinuousPhysicalJointWeight H beta hbeta (A,B) ≤
      Real.exp (16 * beta) *
        originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have h := originalWilsonContinuousPhysicalJointWeight_rightLink_le_exp_sixteen_mul
    H beta hbeta A B e (B e) (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
  simpa only [Function.update_eq_self] using h

/-- Reverse direction, from the actual frozen link to the original B.
This is not a two-sided pointwise statement about arbitrary L2
representatives; it uses the everywhere-positive W_c. -/
theorem originalWilsonContinuousPhysicalJointWeight_frozen_le_exp_sixteen_mul
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ≤
      Real.exp (16 * beta) *
        originalWilsonContinuousPhysicalJointWeight H beta hbeta (A,B) := by
  have h := originalWilsonContinuousPhysicalJointWeight_rightLink_le_exp_sixteen_mul
    H beta hbeta A B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (B e)
  simpa only [Function.update_eq_self] using h

/-- Ratio form: the original continuous Wilson joint density is
bounded by exp(16 beta) times its one-right-link identity-frozen
value. The bound does not depend on the spatial lattice cardinality. -/
theorem originalWilsonContinuousPhysicalJointWeight_div_frozen_le_exp_sixteen
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    originalWilsonContinuousPhysicalJointWeight H beta hbeta (A,B) /
        originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ≤
      Real.exp (16 * beta) := by
  have hpos :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
      (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  exact (div_le_iff₀ hpos).2
    (originalWilsonContinuousPhysicalJointWeight_le_exp_sixteen_mul_frozen
      H beta hbeta A B e)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
