import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalCompletedBoundarySpatialSlicePairL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFixedTimeClassification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance positiveHalfCylinderSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- Number of adjacent Euclidean-time slabs from the primary reflection-fixed
slice at time `0` to the antipodal reflection-fixed slice at time `H+1`.

This is the geometric time exponent that a future path-integral identification
must compare with the actual physical one-slab transfer. -/
def periodicHypercubicEvenPositiveHalfCylinderSlabCount (H : ℕ) : ℕ :=
  H + 1

@[simp] theorem periodicHypercubicEvenPositiveHalfCylinderSlabCount_pos
    (H : ℕ) :
    0 < periodicHypercubicEvenPositiveHalfCylinderSlabCount H := by
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- The full even periodic Euclidean-time circle contains exactly two positive
half-cylinder slab counts. -/
@[simp] theorem periodicHypercubicEvenSideLength_eq_two_mul_positiveHalfCylinderSlabCount
    (H : ℕ) :
    PeriodicHypercubicEvenSideLength H =
      2 * periodicHypercubicEvenPositiveHalfCylinderSlabCount H := by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- Left time endpoint of one slab in the positive reflection half-cylinder. -/
def periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    ZMod (PeriodicHypercubicEvenSideLength H) :=
  (i.1 : ZMod (PeriodicHypercubicEvenSideLength H))

/-- Right time endpoint of one slab in the positive reflection half-cylinder. -/
def periodicHypercubicEvenPositiveHalfCylinderSlabRightTime
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    ZMod (PeriodicHypercubicEvenSideLength H) :=
  ((i.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))

/-- The first positive-half slab starts on the primary fixed plane. -/
@[simp] theorem periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime_zero
    (H : ℕ) :
    periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H 0 = 0 := by
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime]

/-- The last positive-half slab ends on the antipodal fixed plane. -/
@[simp] theorem periodicHypercubicEvenPositiveHalfCylinderSlabRightTime_last
    (H : ℕ) :
    periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H (Fin.last H) =
      ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabRightTime,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- Consecutive positive-half slabs share their intermediate time slice. -/
@[simp] theorem periodicHypercubicEvenPositiveHalfCylinderSlabRightTime_castSucc_eq_leftTime_succ
    (H : ℕ)
    (i : Fin H) :
    periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H i.castSucc =
      periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime H i.succ := by
  simp [periodicHypercubicEvenPositiveHalfCylinderSlabRightTime,
    periodicHypercubicEvenPositiveHalfCylinderSlabLeftTime,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]

/-- Every nonterminal right endpoint in the positive half-cylinder lies in the
strict positive open half.  Thus the intermediate slice times are exactly the
physical residues `1, ..., H`. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSlabRightTime_castSucc_strictPositive
    (H : ℕ)
    (i : Fin H) :
    periodicHypercubicEvenStrictPositiveTime H
      (periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H i.castSucc) := by
  rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
  have hlt : i.1 + 1 < PeriodicHypercubicEvenSideLength H := by
    have hi : i.1 < H := i.2
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  change
    1 ≤ (((i.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val ∧
      (((i.1 + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val ≤ H
  rw [ZMod.val_natCast_of_lt hlt]
  omega

/-- The terminal right endpoint is not in the strict positive open half: it is
the antipodal reflection-fixed slice itself. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSlabRightTime_last_not_strictPositive
    (H : ℕ) :
    ¬ periodicHypercubicEvenStrictPositiveTime H
      (periodicHypercubicEvenPositiveHalfCylinderSlabRightTime H (Fin.last H)) := by
  rw [periodicHypercubicEvenPositiveHalfCylinderSlabRightTime_last]
  rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
  have hlt : H + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  rw [ZMod.val_natCast_of_lt hlt]
  omega

/-- Actual unnormalized physical transfer across the complete positive
reflection half-cylinder.  It is, by definition, the `H+1`-fold power of the
physical one-slab transfer on the Gauss-law Hilbert space.

No path-integral identification with the OS boundary Gram amplitude is asserted
here; this definition fixes the exact operator target for that next theorem. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^
    periodicHypercubicEvenPositiveHalfCylinderSlabCount H

/-- Vacuum-normalized physical transfer across the same positive half-cylinder. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^
    periodicHypercubicEvenPositiveHalfCylinderSlabCount H

/-- Restriction of the normalized positive-half-cylinder transfer to the
orthogonal complement of the complete one-slab top eigenspace. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^
    periodicHypercubicEvenPositiveHalfCylinderSlabCount H

/-- The actual excitation transfer across one positive reflection half-cylinder
inherits the already-proved finite-volume exponential operator-norm decay at
exactly `H+1` one-slab steps. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
        H N hN beta hbeta‖ ≤
      Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_exp_of_pos
      H N hN beta hbeta
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount_pos H)

/-- Every excitation vector has the corresponding exact half-cylinder
finite-volume exponential decay bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_apply_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
        H N hN beta hbeta f‖ ≤
      Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖ := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
      H N hN beta hbeta
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount_pos H) f

/-- Matrix coefficients across the complete positive half-cylinder decay at the
same finite-volume logarithmic rate.  This is still a finite-volume statement;
no uniform-in-`H` lower bound on the rate is asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_matrixCoefficient_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
          H N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
      (Real.exp
        (-(periodicHypercubicEvenPositiveHalfCylinderSlabCount H : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_matrixCoefficient_norm_le_exp_of_pos
      H N hN beta hbeta
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)
      (periodicHypercubicEvenPositiveHalfCylinderSlabCount_pos H) f g

end

end MathlibAnalytic
end MGAP4D
