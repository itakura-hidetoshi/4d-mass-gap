import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianSemigroupCovariance
import Mathlib.Tactic

/-!
# Right derivative of the physical semigroup orbit norm

This layer identifies the positive-time right slope of the squared physical
Hilbert norm with the quadratic form of the canonical right generator, and
hence with minus twice the right Hamiltonian quadratic form.

It is a semigroup/generator statement only.  No spectral theorem, functional
calculus identification `T_t = exp (-t H)`, mass value, PVM atom, or new
physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The normalized positive-time slope of the squared physical orbit norm. -/
def physicalOrbitNormSqSlope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) : ℝ :=
  (t : ℝ)⁻¹ *
    (‖T.toPhysicalSemigroup.operator t psi‖ ^ 2 - ‖psi‖ ^ 2)

/-- The squared-norm slope factors as the real inner product of the canonical
right difference quotient with the sum of the endpoint vectors. -/
theorem physicalOrbitNormSqSlope_eq_inner_rightDifferenceQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) :
    T.physicalOrbitNormSqSlope psi t =
      inner ℝ (T.rightDifferenceQuotient psi t)
        (T.toPhysicalSemigroup.operator t psi + psi) := by
  unfold physicalOrbitNormSqSlope rightDifferenceQuotient
  simp only [real_inner_smul_left, inner_sub_left, inner_add_right,
    real_inner_self_eq_norm_sq]
  have hcross :
      inner ℝ (T.toPhysicalSemigroup.operator t psi) psi =
        inner ℝ psi (T.toPhysicalSemigroup.operator t psi) :=
    real_inner_comm _ _
  rw [hcross]
  ring

/-- On the canonical right-generator domain, the positive-time squared-norm
slope converges to twice the real generator quadratic form. -/
theorem physicalOrbitNormSqSlope_tendsto_rightGenerator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun t : NNReal =>
        T.physicalOrbitNormSqSlope (psi : P.PhysicalHilbert) t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (2 * inner ℝ (T.rightGenerator psi)
          (psi : P.PhysicalHilbert))) := by
  have hgen := T.rightGenerator_hasRightGeneratorValue psi
  unfold HasRightGeneratorValue at hgen
  have horbitFull :
      Tendsto
        (fun t : NNReal =>
          T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert))
        (nhds 0)
        (nhds (psi : P.PhysicalHilbert)) := by
    simpa [T.toPhysicalSemigroup.operator_zero] using
      T.strongContinuousAt_zero (psi : P.PhysicalHilbert)
  have horbit :
      Tendsto
        (fun t : NNReal =>
          T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds (psi : P.PhysicalHilbert)) :=
    horbitFull.mono_left inf_le_left
  have hconst :
      Tendsto
        (fun _ : NNReal => (psi : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds (psi : P.PhysicalHilbert)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun t : NNReal =>
          T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert) +
            (psi : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          ((psi : P.PhysicalHilbert) + (psi : P.PhysicalHilbert))) :=
    horbit.add hconst
  have hinner :
      Tendsto
        (fun t : NNReal =>
          inner ℝ
            (T.rightDifferenceQuotient (psi : P.PhysicalHilbert) t)
            (T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert) +
              (psi : P.PhysicalHilbert)))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (inner ℝ (T.rightGenerator psi)
            ((psi : P.PhysicalHilbert) + (psi : P.PhysicalHilbert)))) :=
    hgen.inner hsum
  have hlimit :
      inner ℝ (T.rightGenerator psi)
          ((psi : P.PhysicalHilbert) + (psi : P.PhysicalHilbert)) =
        2 * inner ℝ (T.rightGenerator psi) (psi : P.PhysicalHilbert) := by
    rw [inner_add_right]
    ring
  rw [hlimit] at hinner
  simpa only [physicalOrbitNormSqSlope_eq_inner_rightDifferenceQuotient] using hinner

/-- In the Euclidean convention `H_right = - generator`, the same right slope
is minus twice the right Hamiltonian quadratic form. -/
theorem physicalOrbitNormSqSlope_tendsto_rightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun t : NNReal =>
        T.physicalOrbitNormSqSlope (psi : P.PhysicalHilbert) t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (-2 * inner ℝ (T.rightHamiltonian psi)
          (psi : P.PhysicalHilbert))) := by
  simpa [T.rightHamiltonian_apply, inner_neg_left] using
    T.physicalOrbitNormSqSlope_tendsto_rightGenerator psi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
