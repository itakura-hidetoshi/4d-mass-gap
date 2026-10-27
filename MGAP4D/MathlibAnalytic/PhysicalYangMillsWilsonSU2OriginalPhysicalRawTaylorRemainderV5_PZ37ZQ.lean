import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticTwoModePhysicalGLPositiveV5_PZ37ZN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonUniformQuadraticRemainderV5_JF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZQ — genuine physical SU(2) Wilson raw fine Taylor remainder

JF proved the EXACT uniform C(Cfg_H, R) Taylor error
  ||RawWilsonHaarRow(t) - 1 - t D_H|| <= (t B_H)^2
on the genuine finite-H one-slab Wilson action-budget window.

JI and JU identify the same spatial Wilson action derivative profile
in actual Haar L², and the ORIGINAL Gauss-law physical U and W_H U
with their genuine continuous representatives.

This file constructs the physical first-order derivative
  D_phys := -(1/2) W_H U - kappa_H U
and the ACTUAL raw transfer error
  E_t := RawPhysicalWilson_t U - U - t D_phys
as elements of the UNMODIFIED Gauss-law physical Hilbert submodule.
Using the exact original raw transfer of U = JF's Wilson Haar row,
the contractive true normalized spatial product-Haar embedding, and
JF's original action-budget estimate, prove unconditionally
  ||E_t||_physical <= (t B_H)^2
on the actual nonnegative fine window ||t B_H|| <= 1.

Unlike generic Wilson analytic test functions, E_t is literally the
physical Gauss-law remainder; no normalization scalar is differentiated.
No new source/posterior model, unproven uniform H radius, new axiom,
sorry, admit, native_decide, compensated Q_GI/N_H floor, endpoint E/F,
H1-H4 or continuum YM gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- True physical derivative of the ORIGINAL raw SU(2) Wilson
Haar constant source: spatial action source plus constant Wilson
crossing-Haar derivative, all in the Gauss-law physical Hilbert. -/
noncomputable def p4Q2PZ37ZQ_originalPhysicalRawDerivative (H : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  (-(1 / 2 : ℝ)) • p4Q2JU_originalSpatialWilsonPhysicalSource H -
    p4Q2JE_originalWilsonHaarZeroDerivativeConstant H •
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2

/-- The physical derivative is exactly JG/JI's genuine strong
Haar-L² Wilson-row derivative: no fake spatial-action test vector. -/
theorem p4Q2PZ37ZQ_originalPhysicalRawDerivative_coe_eq_HaarDerivative
    (H : ℕ) :
    ((p4Q2PZ37ZQ_originalPhysicalRawDerivative H :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
    p4Q2JE_originalWilsonHaarZeroDerivativeLp H := by
  change
    (((-(1 / 2 : ℝ)) • p4Q2JU_originalSpatialWilsonPhysicalSource H -
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        p4Q2JE_originalWilsonHaarZeroDerivativeLp H
  rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H]
  exact (p4Q2JI_actualHaarL2Derivative_eq_spatialAction_and_constant H).symm

/-- The remainder is formed with the actual one-slab physical
SU(2) Wilson transfer of the true physical constant U, not an
independently chosen Haar function or source. -/
noncomputable def p4Q2PZ37ZQ_originalPhysicalRawTaylorError
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 -
    (t : ℝ) • p4Q2PZ37ZQ_originalPhysicalRawDerivative H

/-- The genuine Gauss-law physical error is the exact continuous
spatial Haar-L² image of the ORIGINAL Wilson raw Taylor remainder. -/
theorem p4Q2PZ37ZQ_originalPhysicalRawTaylorError_coe_eq_toLp
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    ((p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
    ContinuousMap.toLp 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
      (p4Q2JF_originalWilsonHaarRowContinuous H (t : ℝ) -
        (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ)) -
        (t : ℝ) • p4Q2JE_originalWilsonHaarZeroDerivativeProfile H) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Raw := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let D := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  change
    ((Raw U - U - (t : ℝ) • D :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 haar) =
      L (p4Q2JF_originalWilsonHaarRowContinuous H (t : ℝ) -
          (1 : C(Cfg, ℝ)) -
          (t : ℝ) • p4Q2JE_originalWilsonHaarZeroDerivativeProfile H)
  rw [Submodule.coe_sub, Submodule.coe_smul,
    p4Q2JI_actualRawFineUnit_coe_eq_HaarRow H (t : ℝ) t.property,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
    p4Q2PZ37ZQ_originalPhysicalRawDerivative_coe_eq_HaarDerivative H,
    ← p4Q2JE_originalWilsonHaarZeroDerivativeLp,
    map_sub, map_smul]

/-- The true physical Taylor remainder is uniformly O_H(t²) on
the true original Wilson finite-volume action-budget window.
The one-slab operator norm normalization is not differentiated. -/
theorem p4Q2PZ37ZQ_originalPhysicalRawTaylorError_norm_le_quadratic
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
    ‖p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t‖ ≤
      ((t : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let eps : C(Cfg, ℝ) :=
    p4Q2JF_originalWilsonHaarRowContinuous H (t : ℝ) -
      (1 : C(Cfg, ℝ)) -
      (t : ℝ) • p4Q2JE_originalWilsonHaarZeroDerivativeProfile H
  have hEmbed :
      ((p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 haar) = L eps :=
    p4Q2PZ37ZQ_originalPhysicalRawTaylorError_coe_eq_toLp H t
  have hL : ‖L‖ ≤ 1 := by
    have h := ContinuousMap.toLp_norm_le
      (α := Cfg) (E := ℝ) (p := (2 : ENNReal)) (𝕜 := ℝ) haar
    simpa [L, measureUnivNNReal] using h
  have hNorm : ‖L eps‖ ≤ ‖eps‖ := by
    calc
      ‖L eps‖ ≤ ‖L‖ * ‖eps‖ := L.le_opNorm eps
      _ ≤ 1 * ‖eps‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg eps)
      _ = ‖eps‖ := one_mul _
  have hJF :
      ‖eps‖ ≤
        ((t : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 :=
    p4Q2JF_originalWilsonHaarRow_supNormQuadraticRemainder_le
      H (t : ℝ) hsmall
  have hEq :
      ‖p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t‖ = ‖L eps‖ :=
    congrArg norm hEmbed
  rw [hEq]
  exact hNorm.trans hJF

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZQ_originalPhysicalRawDerivative_coe_eq_HaarDerivative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZQ_originalPhysicalRawTaylorError_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZQ_originalPhysicalRawTaylorError_norm_le_quadratic
