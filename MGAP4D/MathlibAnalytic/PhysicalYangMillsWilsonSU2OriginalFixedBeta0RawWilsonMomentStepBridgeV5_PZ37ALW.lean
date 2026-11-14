import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0GeometricVolumeStepNormBudgetV5_PZ37ALV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALW — physical raw-Wilson moment step to normalized gap

The original fixed beta0=log(3/2)/64 finite-volume physical SU(2)
Wilson operators P_H and normalized excited restrictions R_H live on
different H-dependent Hilbert spaces. Comparing these OPERATOR VALUES
across H is not type correct without a separately proved transport.

The earlier ALN proves the actual strictly positive ALJ moment floor
  0 < F_H <= ||P_H||
and the raw-physical pointwise operator norm bridge
  (forall x in K_H, ||P_H x|| <= q*F_H*||x||) => ||R_H|| <= q.

ALV proves that a summable scalar increase in ||R_H||^2 suffices for a
positive original-beta0 all-finite-volume gap.

Here we explicitly compose these genuine-model results without changing
operators, Haar measure, AJA budgets, original beta0 or any assumption.
The physical input is a DIRECT raw kernel/transfer estimate at volume
H+1 relative to the preceding REAL scalar Q_H=||R_H||^2:

  ||P_(H+1) x|| <= sqrt(Q_H+b_H) * F_(H+1) * ||x||, x in K_(H+1).

This is a strictly stronger physical premise than the desired normalized
step estimate, since F_(H+1) <= ||P_(H+1)||. It must be independently
established from the genuine Wilson kernel and Haar geometry, not from a
generic operator norm inequality.

We prove that the concrete original-physical raw moment premise implies
Q_(H+1)<=Q_H+b_H and hence the exact ALU downward loss bound.
A finite total step budget or a geometric b_H=C*r^H then yields the
conditional all-H original-beta0 gap. An explicit obstruction shows
failure of the raw moment premise whenever the actual norm increase
exceeds its proposed b_H.

NO such physical raw step estimate, summability, fixed-beta0 all-H gap,
Hamiltonian gap or 4D continuum Yang-Mills mass gap is claimed here.
One append-only Lean leaf; fixed Lean/mathlib and same-root governance.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "Q" => p4Q2PZ37ALV_originalFixedExcitedNormSq
local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "F" => p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor
local notation "L" => p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt

/-- Model-facing NEXT-volume physical Wilson raw moment step certificate.
The only previous-volume datum is the real scalar Q_H, not a vector or
operator on the non-isomorphic Hilbert space at volume H. -/
def p4Q2PZ37ALW_originalFixedRawMomentStepCertificate (H : ℕ) (b : ℝ) : Prop :=
  ∀ x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le,
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
        (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (H + 1) 2)‖ ≤
      Real.sqrt (Q H + b) * F (H + 1) *
        ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (H + 1) 2)‖

/-- EXACT genuine Wilson raw-to-normalized step bridge.  The ALN
positive moment-floor estimate supplies the physical normalizer;
the norm-square estimate is on REAL numbers, not cross-volume carriers. -/
theorem p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hRaw : p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H b) :
    Q (H + 1) ≤ Q H + b := by
  have hq0 : 0 ≤ Q H := by
    unfold p4Q2PZ37ALV_originalFixedExcitedNormSq
    positivity
  have hq : 0 ≤ Q H + b := add_nonneg hq0 hb
  have hNorm :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤
        Real.sqrt (Q H + b) := by
    exact p4Q2PZ37ALN_originalFixedNormalizedRestriction_norm_le_of_rawMomentBound
      (H + 1) (Real.sqrt (Q H + b)) (Real.sqrt_nonneg _) hRaw
  have hSquare :
      Q (H + 1) ≤ (Real.sqrt (Q H + b)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hNorm
  simpa only [Real.sq_sqrt hq] using hSquare

/-- Any independent scalar upper certificate a for the TRUE raw physical
Wilson operator on the full K_(H+1) sector can feed the same criterion.
The scalar comparison a <= sqrt(Q_H+b)*F_(H+1) is a distinct,
still-unproved physical ingredient. -/
theorem p4Q2PZ37ALW_rawMomentStep_of_independentRawCeiling
    (H : ℕ) (b a : ℝ)
    (hRawCeiling : ∀ x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (H + 1) 2)‖ ≤
        a * ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (H + 1) 2)‖)
    (hCompare : a ≤ Real.sqrt (Q H + b) * F (H + 1)) :
    p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H b := by
  intro x
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        (H + 1) 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
        (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (H + 1) 2)‖ ≤
      a * ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (H + 1) 2)‖ := hRawCeiling x
    _ ≤ (Real.sqrt (Q H + b) * F (H + 1)) *
      ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (H + 1) 2)‖ :=
      mul_le_mul_of_nonneg_right hCompare (norm_nonneg _)
    _ = _ := by ring

/-- A raw physical Wilson step certificate controls the ACTUAL smallest
ALU scalar downward variation in one physical volume increment. -/
theorem p4Q2PZ37ALW_rawMomentStep_implies_downwardLoss_le
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hRaw : p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H b) :
    L H ≤ b := by
  exact p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease
    H b hb (p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep H b hb hRaw)

/-- A uniform upper bound on the sum of INDEPENDENT genuine raw Wilson
one-volume moment penalties yields a strictly positive fixed-beta0 gap.
Neither the raw physical estimates nor their total budget is asserted. -/
theorem p4Q2PZ37ALW_uniformGap_of_rawMomentStepSummableBudget
    (b : ℕ → ℝ) (B : ℝ)
    (hb : ∀ H : ℕ, 0 ≤ b H)
    (hRaw : ∀ H : ℕ,
      p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H (b H))
    (htotal : ∀ H : ℕ, (Finset.range H).sum b ≤ B)
    (hstrict : B < D 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have hstep : ∀ H : ℕ, D H ≤ D (H + 1) + b H := by
    intro H
    have hl := p4Q2PZ37ALW_rawMomentStep_implies_downwardLoss_le
      H (b H) (hb H) (hRaw H)
    have hd := p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit H
    linarith
  exact p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
    b B hb hstep htotal hstrict

/-- The original beta0 all-H spectral gap follows CONDITIONALLY from
direct original Wilson raw-moment step control with a geometric summable
budget at every finite volume; no such Wilson bound is established. -/
theorem p4Q2PZ37ALW_uniformGap_of_rawMomentGeometricBudget
    (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D 0)
    (hRaw : ∀ H : ℕ,
      p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H (C * r ^ H)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  apply p4Q2PZ37ALV_uniformGap_of_global_geometricNormSqStep
    C r hC hr0 hr1 hSmall
  intro H
  exact p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep
    H (C * r ^ H) (mul_nonneg hC (pow_nonneg hr0 H)) (hRaw H)

/-- The model-facing geometric raw moment estimates may be supplied ONLY
on the tail H>=M; ALT handles every H<=M unconditionally.
The strict threshold C < (1-r)*delta_M remains a true physical budget. -/
theorem p4Q2PZ37ALW_uniformGap_of_tail_rawMomentGeometricBudget
    (M : ℕ) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D M)
    (hRawTail : ∀ n : ℕ,
      p4Q2PZ37ALW_originalFixedRawMomentStepCertificate (M + n) (C * r ^ n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  apply p4Q2PZ37ALV_uniformGap_of_tail_geometricNormSqStep
    M C r hC hr0 hr1 hSmall
  intro n
  exact p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep
    (M + n) (C * r ^ n) (mul_nonneg hC (pow_nonneg hr0 n)) (hRawTail n)

/-- Explicit physical-test obstruction. A proposed raw physical
moment-step estimate with budget b is IMPOSSIBLE if the actual scalar
excited norm-square increase already exceeds that same budget. -/
theorem p4Q2PZ37ALW_rawMomentStep_impossible_of_excessNormSqIncrease
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hExcess : Q H + b < Q (H + 1)) :
    ¬ p4Q2PZ37ALW_originalFixedRawMomentStepCertificate H b := by
  intro hRaw
  have hNorm := p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep
    H b hb hRaw
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_originalFixedRawMomentStepCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_rawMomentStep_implies_excitedNormSqStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_rawMomentStep_of_independentRawCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_rawMomentStep_implies_downwardLoss_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_uniformGap_of_rawMomentStepSummableBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_uniformGap_of_rawMomentGeometricBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_uniformGap_of_tail_rawMomentGeometricBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALW_rawMomentStep_impossible_of_excessNormSqIncrease
