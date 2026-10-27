import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRankOneNormVacuumQuadraticV5_PZ37ZU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZV — genuine physical SU(2) Wilson raw top-norm first variation

At each fixed finite physical H, the true raw Wilson transfer R_t, unit
Gauss-law Haar vacuum U_H and physical derivative
D_H = -W_H/2 - kappa_H U_H satisfy (ZQ)
  ‖R_t U_H - U_H - t D_H‖ ≤ (t B_H)^2.
ZU established the TRUE rank-one top norm/physical vacuum inequality
  0 ≤ ‖R_t‖ - ⟪R_t U_H,U_H⟫ ≤ 8 (t B_H)^2
for B_H t ≤ 1/4.

Here the actual Haar vacuum expectation is identified to second order
with 1 + t ⟪D_H,U_H⟫. Combining the SAME true Wilson operators,
  |‖R_t‖ - (1 + t ⟪D_H,U_H⟫)| ≤ 9 (t B_H)^2.

The coefficient is the genuine spatial Wilson Haar mean:
  ⟪D_H,U_H⟫ = -kappa_H - ⟪W_H U_H,U_H⟫ / 2.

No differentiation of the operator norm, no auxiliary source/posterior,
no new axioms/sorry/admit/native_decide, no volume/scale-uniform window,
no H1-H4 and no continuum 4D Yang–Mills mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The TRUE vacuum response of the original finite-H raw transfer
has the same first-order coefficient as the physical Gauss-law
Taylor vector D_H, with its exact second-order error. -/
theorem p4Q2PZ37ZV_originalRawVacuumExpectation_firstOrder_error
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
    |inner ℝ
       (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
         H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
         (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
       (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
       (1 + (t : ℝ) * inner ℝ
         (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
         (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))| ≤
      ((t : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let D : Phys := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  let E : Phys := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  let R : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hU : ‖U‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hRaw : R U = U + (t : ℝ) • D + E := by
    change R U = U + (t : ℝ) • D + (R U - U - (t : ℝ) • D)
    abel
  have hInner : inner ℝ (R U) U =
      1 + (t : ℝ) * inner ℝ D U + inner ℝ E U := by
    calc
      inner ℝ (R U) U =
          inner ℝ (U + (t : ℝ) • D + E) U :=
        congrArg (fun x : Phys => inner ℝ x U) hRaw
      _ = inner ℝ (U + (t : ℝ) • D) U + inner ℝ E U :=
        inner_add_left _ _ _
      _ = inner ℝ U U + inner ℝ ((t : ℝ) • D) U +
            inner ℝ E U := by
        exact congrArg (fun z : ℝ => z + inner ℝ E U)
          (inner_add_left U ((t : ℝ) • D) U)
      _ = 1 + (t : ℝ) * inner ℝ D U + inner ℝ E U := by
        have hs : inner ℝ ((t : ℝ) • D) U =
            (t : ℝ) * inner ℝ D U :=
          real_inner_smul_left D U (t : ℝ)
        have hUU : inner ℝ U U = 1 := by
          calc
            inner ℝ U U = ‖U‖^2 := real_inner_self_eq_norm_sq U
            _ = 1 := by rw [hU]; norm_num
        rw [hs, hUU]
        ring
  have hE : ‖E‖ ≤ ((t : ℝ) * B)^2 :=
    p4Q2PZ37ZQ_originalPhysicalRawTaylorError_norm_le_quadratic H t hsmall
  have hInnerError : |inner ℝ E U| ≤ ‖E‖ := by
    calc
      |inner ℝ E U| ≤ ‖E‖ * ‖U‖ := abs_real_inner_le_norm E U
      _ = ‖E‖ := by rw [hU, mul_one]
  change |inner ℝ (R U) U -
    (1 + (t : ℝ) * inner ℝ D U)| ≤ ((t : ℝ) * B)^2
  rw [hInner]
  have hIdentity :
      (1 + (t : ℝ) * inner ℝ D U + inner ℝ E U) -
        (1 + (t : ℝ) * inner ℝ D U) = inner ℝ E U := by ring
  rw [hIdentity]
  exact hInnerError.trans hE

/-- The ORIGINAL full physical raw Wilson top operator norm shares
the true physical vacuum linear response. The remainder is O_H(t²),
with explicit coefficient 9 B_H², and the actual rank-one budget. -/
theorem p4Q2PZ37ZV_originalPhysicalRawNorm_firstOrder_error
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hsmall : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      (t : ℝ) ≤ (1 / 4 : ℝ)) :
    |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
         H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ -
      (1 + (t : ℝ) * inner ℝ
        (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))| ≤
      9 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ))^2 := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let D : Phys := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  let R : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have ht : 0 ≤ (t : ℝ) := t.property
  have hsmallOne : ‖(t : ℝ) * B‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht hB)]
    nlinarith [hsmall]
  obtain ⟨hGapNonneg, hGapBound⟩ :=
    p4Q2PZ37ZU_originalPhysicalRawTopNorm_vacuum_gap_quadratic H t hsmall
  have hVacuum :
      |inner ℝ (R U) U - (1 + (t : ℝ) * inner ℝ D U)| ≤
      ((t : ℝ) * B)^2 :=
    p4Q2PZ37ZV_originalRawVacuumExpectation_firstOrder_error H t hsmallOne
  have hGapAbs :
      |‖R‖ - inner ℝ (R U) U| ≤ 8 * (B * (t : ℝ))^2 := by
    rw [abs_of_nonneg hGapNonneg]
    exact hGapBound
  change |‖R‖ - (1 + (t : ℝ) * inner ℝ D U)| ≤ 9 * (B * (t : ℝ))^2
  calc
    |‖R‖ - (1 + (t : ℝ) * inner ℝ D U)| =
        |(‖R‖ - inner ℝ (R U) U) +
          (inner ℝ (R U) U - (1 + (t : ℝ) * inner ℝ D U))| := by
        congr 1
        ring
    _ ≤ |‖R‖ - inner ℝ (R U) U| +
          |inner ℝ (R U) U - (1 + (t : ℝ) * inner ℝ D U)| := abs_add_le _ _
    _ ≤ 8 * (B * (t : ℝ))^2 + ((t : ℝ) * B)^2 :=
      add_le_add hGapAbs hVacuum
    _ = 9 * (B * (t : ℝ))^2 := by ring

/-- The first-order scalar is the ORIGINAL Gauss-law Wilson action
Haar mean plus the exact crossing-Haar constant, not a new
spectral normalization derivative. -/
theorem p4Q2PZ37ZV_originalPhysicalRawDerivative_vacuum_coeff
    (H : ℕ) :
    inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
      -(1 / 2 : ℝ) * inner ℝ
        (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let k : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  have hU : ‖U‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  change inner ℝ ((-(1 / 2 : ℝ)) • W - k • U) U =
      -(1 / 2 : ℝ) * inner ℝ W U - k
  calc
    inner ℝ ((-(1 / 2 : ℝ)) • W - k • U) U =
        inner ℝ ((-(1 / 2 : ℝ)) • W) U -
          inner ℝ (k • U) U :=
      inner_sub_left _ _ _
    _ = -(1 / 2 : ℝ) * inner ℝ W U - k := by
      have hsW : inner ℝ ((-(1 / 2 : ℝ)) • W) U =
          -(1 / 2 : ℝ) * inner ℝ W U :=
        real_inner_smul_left W U (-(1 / 2 : ℝ))
      have hsU : inner ℝ (k • U) U = k * inner ℝ U U :=
        real_inner_smul_left U U k
      have hUU : inner ℝ U U = 1 := by
        calc
          inner ℝ U U = ‖U‖^2 := real_inner_self_eq_norm_sq U
          _ = 1 := by rw [hU]; norm_num
      rw [hsW, hsU, hUU]
      ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV_originalRawVacuumExpectation_firstOrder_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV_originalPhysicalRawNorm_firstOrder_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV_originalPhysicalRawDerivative_vacuum_coeff
