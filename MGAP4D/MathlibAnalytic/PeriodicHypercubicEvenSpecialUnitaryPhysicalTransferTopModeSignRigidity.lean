import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopModeRigidity
import Mathlib.Tactic

/-!
# Sign rigidity of finite-volume physical Wilson top modes

The previous layer proves that every nonzero nonnegative vector in the full
normalized physical top eigenspace is strictly positive almost everywhere.

Here the absolute-value comparison is upgraded to a rigidity statement:
for every unit top mode `f`, its pointwise absolute value `|f|` is again a
top mode. Therefore both `|f| + f` and `|f| - f` are nonnegative top modes.
Their pointwise product is identically zero. They cannot both be nonzero,
because the previous strict-positivity theorem would make both factors strictly
positive almost everywhere.

Hence every unit top mode has one fixed sign almost everywhere.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance physicalTopSignRigidityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalTopSignRigidityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalTopSignRigiditySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalTopSignRigidityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalTopSignRigidityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalTopSignRigiditySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section PhysicalTopSignRigidity

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

/-- The physical absolute value of a unit top mode is again in the full top
eigenspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_mem_topEigenspace_of_unit
    (f : G)
    (hfTop : f ∈ F)
    (hfNorm : ‖f‖ = 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f ∈ F := by
  let T0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let a :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f
  have hTpos : 0 < ‖T0‖ := by
    simpa [T0] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hfix :
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f = f :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta f).1 hfTop
  have hraw : T0 f = ‖T0‖ • f := by
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
      at hfix
    change ‖T0‖⁻¹ • T0 f = f at hfix
    have hscaled := congrArg (fun z : G => ‖T0‖ • z) hfix
    simpa [smul_smul, hTpos.ne'] using hscaled
  have hfQuad : inner ℝ (T0 f) f = ‖T0‖ :=
    realHilbert_inner_eq_opNorm_of_unit_eigen T0 f hfNorm hraw
  have haNorm : ‖a‖ = 1 := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_norm H N f
    exact h.trans hfNorm
  have hdom : inner ℝ (T0 f) f ≤ inner ℝ (T0 a) a := by
    simpa [T0, a] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_le_abs
        H N hN beta hbeta f)
  have hupper : inner ℝ (T0 a) a ≤ ‖T0‖ := by
    calc
      inner ℝ (T0 a) a ≤ ‖T0 a‖ * ‖a‖ := real_inner_le_norm _ _
      _ ≤ (‖T0‖ * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.le_opNorm T0 a) (norm_nonneg a)
      _ = ‖T0‖ := by rw [haNorm]; ring
  have haQuad : inner ℝ (T0 a) a = ‖T0‖ := by
    exact le_antisymm hupper (hfQuad ▸ hdom)
  have haRaw : T0 a = ‖T0‖ • a :=
    realHilbert_eigen_of_unit_inner_eq_opNorm T0 a haNorm haQuad
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  change ‖T0‖⁻¹ • T0 a = a
  rw [haRaw, smul_smul, inv_mul_cancel₀ hTpos.ne', one_smul]

/-- Every unit vector in the full physical top eigenspace has one fixed sign
almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_unit_sign_rigidity
    (f : G)
    (hfTop : f ∈ F)
    (hfNorm : ‖f‖ = 1) :
    (∀ᵐ A ∂μ, 0 ≤ (f : Lp ℝ 2 μ) A) ∨
      (∀ᵐ A ∂μ, (f : Lp ℝ 2 μ) A ≤ 0) := by
  let a : G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f
  let p : G := a + f
  let n : G := a - f
  have haTop : a ∈ F := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_mem_topEigenspace_of_unit
        H N hN beta hbeta f hfTop hfNorm
  have hpTop : p ∈ F := by
    exact Submodule.add_mem F haTop hfTop
  have hnTop : n ∈ F := by
    exact Submodule.sub_mem F haTop hfTop
  have haCoe :
      (fun A => (a : Lp ℝ 2 μ) A) =ᵐ[μ]
        fun A => |(f : Lp ℝ 2 μ) A| := by
    change
      realL2Abs (f : Lp ℝ 2 μ) =ᵐ[μ]
        fun A => |(f : Lp ℝ 2 μ) A|
    exact realL2Abs_coeFn (f : Lp ℝ 2 μ)
  have hpCoe :
      (fun A => (p : Lp ℝ 2 μ) A) =ᵐ[μ]
        fun A => |(f : Lp ℝ 2 μ) A| + (f : Lp ℝ 2 μ) A := by
    have hAdd :=
      Lp.coeFn_add (a : Lp ℝ 2 μ) (f : Lp ℝ 2 μ)
    filter_upwards [hAdd, haCoe] with A hAddA hAbs
    calc
      (p : Lp ℝ 2 μ) A =
          ((a : Lp ℝ 2 μ) + (f : Lp ℝ 2 μ)) A := by rfl
      _ = ((fun x => (a : Lp ℝ 2 μ) x) +
          (fun x => (f : Lp ℝ 2 μ) x)) A := hAddA
      _ = (a : Lp ℝ 2 μ) A + (f : Lp ℝ 2 μ) A := by rfl
      _ = |(f : Lp ℝ 2 μ) A| + (f : Lp ℝ 2 μ) A := by rw [hAbs]
  have hnCoe :
      (fun A => (n : Lp ℝ 2 μ) A) =ᵐ[μ]
        fun A => |(f : Lp ℝ 2 μ) A| - (f : Lp ℝ 2 μ) A := by
    have hSub :=
      Lp.coeFn_sub (a : Lp ℝ 2 μ) (f : Lp ℝ 2 μ)
    filter_upwards [hSub, haCoe] with A hSubA hAbs
    calc
      (n : Lp ℝ 2 μ) A =
          ((a : Lp ℝ 2 μ) - (f : Lp ℝ 2 μ)) A := by rfl
      _ = ((fun x => (a : Lp ℝ 2 μ) x) -
          (fun x => (f : Lp ℝ 2 μ) x)) A := hSubA
      _ = (a : Lp ℝ 2 μ) A - (f : Lp ℝ 2 μ) A := by rfl
      _ = |(f : Lp ℝ 2 μ) A| - (f : Lp ℝ 2 μ) A := by rw [hAbs]
  have hpNonneg : ∀ᵐ A ∂μ, 0 ≤ (p : Lp ℝ 2 μ) A := by
    filter_upwards [hpCoe] with A hEq
    rw [hEq]
    linarith [neg_le_abs ((f : Lp ℝ 2 μ) A)]
  have hnNonneg : ∀ᵐ A ∂μ, 0 ≤ (n : Lp ℝ 2 μ) A := by
    filter_upwards [hnCoe] with A hEq
    rw [hEq]
    linarith [le_abs_self ((f : Lp ℝ 2 μ) A)]
  have hprodZero :
      ∀ᵐ A ∂μ, (p : Lp ℝ 2 μ) A * (n : Lp ℝ 2 μ) A = 0 := by
    filter_upwards [hpCoe, hnCoe] with A hpEq hnEq
    rw [hpEq, hnEq]
    calc
      (|(f : Lp ℝ 2 μ) A| + (f : Lp ℝ 2 μ) A) *
          (|(f : Lp ℝ 2 μ) A| - (f : Lp ℝ 2 μ) A) =
        |(f : Lp ℝ 2 μ) A| ^ 2 - (f : Lp ℝ 2 μ) A ^ 2 := by ring
      _ = 0 := by rw [sq_abs]; ring
  have hzero : p = 0 ∨ n = 0 := by
    by_cases hpZero : p = 0
    · exact Or.inl hpZero
    · right
      by_contra hnZero
      have hpPos :
          ∀ᵐ A ∂μ, 0 < (p : Lp ℝ 2 μ) A :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_ae_pos_of_nonnegative_ne_zero
          H N hN beta hbeta p hpTop hpNonneg hpZero
      have hnPos :
          ∀ᵐ A ∂μ, 0 < (n : Lp ℝ 2 μ) A :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_ae_pos_of_nonnegative_ne_zero
          H N hN beta hbeta n hnTop hnNonneg hnZero
      obtain ⟨A, hpA, hnA, hzeroA⟩ :=
        (hpPos.and (hnPos.and hprodZero)).exists
      have hmul : 0 < (p : Lp ℝ 2 μ) A * (n : Lp ℝ 2 μ) A :=
        mul_pos hpA hnA
      rw [hzeroA] at hmul
      exact (lt_irrefl 0) hmul
  rcases hzero with hpZero | hnZero
  · right
    have hpZeroAe : ∀ᵐ A ∂μ, (p : Lp ℝ 2 μ) A = 0 := by
      rw [hpZero]
      simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
    filter_upwards [hpCoe, hpZeroAe] with A hpEq hz
    rw [hpEq] at hz
    by_contra hnot
    have hpos : 0 < (f : Lp ℝ 2 μ) A := lt_of_not_ge hnot
    rw [abs_of_pos hpos] at hz
    linarith
  · left
    have hnZeroAe : ∀ᵐ A ∂μ, (n : Lp ℝ 2 μ) A = 0 := by
      rw [hnZero]
      simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
    filter_upwards [hnCoe, hnZeroAe] with A hnEq hz
    rw [hnEq] at hz
    by_contra hnot
    have hneg : (f : Lp ℝ 2 μ) A < 0 := lt_of_not_ge hnot
    rw [abs_of_neg hneg] at hz
    linarith

end PhysicalTopSignRigidity

end

end MathlibAnalytic
end MGAP4D
