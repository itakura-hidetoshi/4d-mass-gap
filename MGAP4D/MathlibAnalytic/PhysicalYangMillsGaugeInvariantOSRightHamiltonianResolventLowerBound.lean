import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianNonnegative
import Mathlib.Tactic

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

/-- The positive resolvent shift `lambda I + H` on the canonical right
Hamiltonian domain. -/
noncomputable def rightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ) :
    T.rightGeneratorDomain →ₗ[ℝ] P.PhysicalHilbert :=
  lambda • T.rightGeneratorDomain.subtype + T.rightHamiltonian

@[simp] theorem rightHamiltonianShift_apply
    (T : P.StronglyContinuousPhysicalSemigroup) (lambda : ℝ)
    (psi : T.rightGeneratorDomain) :
    T.rightHamiltonianShift lambda psi =
      lambda • (psi : P.PhysicalHilbert) + T.rightHamiltonian psi := by
  rfl

/-- The positive resolvent shift satisfies the Hille--Yosida lower bound on the
canonical domain.  This uses only accretivity of the right Hamiltonian. -/
theorem lambda_mul_norm_le_norm_rightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi : T.rightGeneratorDomain) :
    lambda * ‖(psi : P.PhysicalHilbert)‖ ≤
      ‖T.rightHamiltonianShift lambda psi‖ := by
  have hquad :
      lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        ⟪T.rightHamiltonianShift lambda psi,
          (psi : P.PhysicalHilbert)⟫_ℝ := by
    rw [T.rightHamiltonianShift_apply, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [T.rightHamiltonian_inner_nonneg psi]
  have hcs :
      ⟪T.rightHamiltonianShift lambda psi,
          (psi : P.PhysicalHilbert)⟫_ℝ ≤
        ‖T.rightHamiltonianShift lambda psi‖ *
          ‖(psi : P.PhysicalHilbert)‖ :=
    real_inner_le_norm _ _
  have hmul :
      lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        ‖T.rightHamiltonianShift lambda psi‖ *
          ‖(psi : P.PhysicalHilbert)‖ :=
    hquad.trans hcs
  by_cases hzero : ‖(psi : P.PhysicalHilbert)‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hmul]

/-- A positive resolvent shift has trivial kernel. -/
theorem rightHamiltonianShift_eq_zero_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi : T.rightGeneratorDomain) :
    T.rightHamiltonianShift lambda psi = 0 ↔ psi = 0 := by
  constructor
  · intro hpsi
    have hbound :=
      T.lambda_mul_norm_le_norm_rightHamiltonianShift hlambda psi
    rw [hpsi, norm_zero] at hbound
    have hnorm : ‖(psi : P.PhysicalHilbert)‖ = 0 := by
      have hnonneg : 0 ≤ ‖(psi : P.PhysicalHilbert)‖ := norm_nonneg _
      nlinarith
    apply Subtype.ext
    exact norm_eq_zero.mp hnorm
  · intro hpsi
    subst psi
    simp

/-- Every positive resolvent shift of the right Hamiltonian is injective. -/
theorem rightHamiltonianShift_injective
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Injective (T.rightHamiltonianShift lambda) := by
  intro psi phi hpsiPhi
  have hzero : T.rightHamiltonianShift lambda (psi - phi) = 0 := by
    rw [map_sub, hpsiPhi, sub_self]
  have hz : psi - phi = 0 :=
    (T.rightHamiltonianShift_eq_zero_iff hlambda (psi - phi)).mp hzero
  exact sub_eq_zero.mp hz

/-- The resolvent lower bound and injectivity package the part of maximal
accretivity already forced by contraction and strong continuity.  Surjectivity
of the shift is deliberately not asserted here. -/
theorem rightHamiltonian_positiveShift_lowerBound_and_injective
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (∀ psi : T.rightGeneratorDomain,
      lambda * ‖(psi : P.PhysicalHilbert)‖ ≤
        ‖T.rightHamiltonianShift lambda psi‖) ∧
      Function.Injective (T.rightHamiltonianShift lambda) :=
  ⟨T.lambda_mul_norm_le_norm_rightHamiltonianShift hlambda,
    T.rightHamiltonianShift_injective hlambda⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
