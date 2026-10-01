import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Tactic

/-!
# Strict positivity rigidity for finite-volume physical Wilson top modes

The literal one-slab Wilson kernel is strictly positive. Earlier layers used
that fact to construct one strictly positive top eigenvector but deliberately
did not assert simplicity of the full top eigenspace.

This file begins the missing rigidity argument. Any full-top vector which is
nonnegative almost everywhere is automatically strictly positive almost
everywhere, provided it is nonzero.

No Perron--Frobenius simplicity theorem is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance physicalTopRigidityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalTopRigidityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalTopRigiditySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalTopRigidityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalTopRigidityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalTopRigiditySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section PhysicalTopRigidity

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "μ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta

local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta

local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta

/-- A unit nonnegative vector in the full normalized-transfer top eigenspace is
strictly positive almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_ae_pos_of_nonnegative_unit
    (f : G)
    (hfTop : f ∈ F)
    (hfNonneg : ∀ᵐ A ∂μ, 0 ≤ (f : Lp ℝ 2 μ) A)
    (hfNorm : ‖f‖ = 1) :
    ∀ᵐ A ∂μ, 0 < (f : Lp ℝ 2 μ) A := by
  let lambda : ℝ := ‖T‖
  have hlambda : 0 < lambda := by
    simpa [lambda] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hfix : S f = f :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta f).1 hfTop
  have hraw : T f = lambda • f := by
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
      at hfix
    change lambda⁻¹ • T f = f at hfix
    calc
      T f = 1 • T f := by simp
      _ = (lambda * lambda⁻¹) • T f := by
        rw [mul_inv_cancel₀ hlambda.ne']
      _ = lambda • (lambda⁻¹ • T f) := by
        rw [smul_smul]
      _ = lambda • f := by rw [hfix]
  have hrawAmbient :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta (f : Lp ℝ 2 μ) =
        lambda • (f : Lp ℝ 2 μ) := by
    have h := congrArg Subtype.val hraw
    simpa using h
  obtain ⟨c, hc, hLower⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_ae_ge_pos_const
      H N hN beta hbeta (f : Lp ℝ 2 μ) hfNonneg hfNorm
  have hrawCoe :
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta (f : Lp ℝ 2 μ) A) =ᵐ[μ]
        fun A => lambda * (f : Lp ℝ 2 μ) A := by
    rw [hrawAmbient]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Lp.coeFn_smul lambda (f : Lp ℝ 2 μ)
  filter_upwards [hLower, hrawCoe] with A hA hEq
  rw [hEq] at hA
  have hprod : 0 < lambda * (f : Lp ℝ 2 μ) A :=
    lt_of_lt_of_le hc hA
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge hlambda.le) hneg.1)

/-- A nonzero nonnegative vector in the full top eigenspace is strictly
positive almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_ae_pos_of_nonnegative_ne_zero
    (f : G)
    (hfTop : f ∈ F)
    (hfNonneg : ∀ᵐ A ∂μ, 0 ≤ (f : Lp ℝ 2 μ) A)
    (hfNe : f ≠ 0) :
    ∀ᵐ A ∂μ, 0 < (f : Lp ℝ 2 μ) A := by
  have hfNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  let a : ℝ := ‖f‖⁻¹
  let u : G := a • f
  have ha : 0 < a := by
    exact inv_pos.mpr hfNormPos
  have huTop : u ∈ F := by
    exact F.smul_mem a hfTop
  have huNorm : ‖u‖ = 1 := by
    dsimp [u, a]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hfNormPos]
    exact inv_mul_cancel₀ hfNormPos.ne'
  have huNonneg : ∀ᵐ A ∂μ, 0 ≤ (u : Lp ℝ 2 μ) A := by
    have huCoe :
        (fun A => (u : Lp ℝ 2 μ) A) =ᵐ[μ]
          fun A => a * (f : Lp ℝ 2 μ) A := by
      dsimp [u]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        Lp.coeFn_smul a (f : Lp ℝ 2 μ)
    filter_upwards [huCoe, hfNonneg] with A hEq hA
    rw [hEq]
    exact mul_nonneg ha.le hA
  have huPos : ∀ᵐ A ∂μ, 0 < (u : Lp ℝ 2 μ) A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_ae_pos_of_nonnegative_unit
      H N hN beta hbeta u huTop huNonneg huNorm
  have huCoe :
      (fun A => (u : Lp ℝ 2 μ) A) =ᵐ[μ]
        fun A => a * (f : Lp ℝ 2 μ) A := by
    dsimp [u]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Lp.coeFn_smul a (f : Lp ℝ 2 μ)
  filter_upwards [huPos, huCoe] with A hPos hEq
  rw [hEq] at hPos
  rcases (mul_pos_iff.mp hPos) with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge ha.le) hneg.1)

end PhysicalTopRigidity

end

end MathlibAnalytic
end MGAP4D
