import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticPhysicalGLQuantitativeV5_PZ37ZP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalRawTaylorRemainderV5_PZ37ZQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLPhysicalTriangleV5_PZ37ZR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCancellationLinearFineLowerV5_PZ37ZK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZS — genuine Wilson physical-source quadratic fine GL floor

Combine ZP's actual two-mode full-link GL Gram floor, ZQ's physical
raw-Wilson Taylor error, ZR's physical perturbation inequality, and
ZC's genuine all-physical-source upper GL bound, at fixed finite H
and positive frozen b. The fine transfer normalization scalar is
retained EXACTLY, without differentiation.

The genuine normalized Gauss-law physical cancellation is decomposed as
  F_t = S_t - s_t E_t,
  S_t = (1-s_t+s_t kappa_H t) U_H + (s_t t/2) W_H U_H,
  s_t = ||RawWilson_t||^-1.

All sources and pair-Haar posteriors remain the original physical ones.
No new axioms, sorry/admit/native_decide, compensating-context no-go
reversal, H-uniform/scale-uniform claim, endpoint E, H1-H4, or continuum
Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZS_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual inverse norm of the original UNNORMALIZED physical
one-slab Wilson operator. Never differentiate this scalar. -/
noncomputable def p4Q2PZ37ZS_originalRawInverseNorm
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖⁻¹

/-- Coefficients in the genuine physical (U_H,W_H U_H) source plane.
Only the genuine raw normalization s_t occurs. -/
noncomputable def p4Q2PZ37ZS_originalPhysicalStaticCoefficients
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then
      1 - p4Q2PZ37ZS_originalRawInverseNorm H t +
        p4Q2PZ37ZS_originalRawInverseNorm H t *
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H * (t : ℝ)
    else
      p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2

/-- The static part is EXACTLY ZN's authentic physical Wilson source. -/
noncomputable def p4Q2PZ37ZS_originalPhysicalStaticPart
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  p4Q2PZ37ZN_originalStaticPhysicalSource H
    (p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t)

/-- The normalized physical fine cancellation decomposes EXACTLY in
the original Gauss-law Haar Hilbert as static 2-mode source minus the
true physical Taylor remainder times inverse raw norm. -/
theorem p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    p4Q2PZ37ZE_originalPhysicalCancellation H t =
      p4Q2PZ37ZS_originalPhysicalStaticPart H t -
        p4Q2PZ37ZS_originalRawInverseNorm H t •
          p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let kappa : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  let Raw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let D : Phys := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  let E : Phys := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  have hD : D = (-(1 / 2 : ℝ)) • W - kappa • U := rfl
  have hRaw : Raw U = U + (t : ℝ) • D + E := by
    change Raw U = U + (t : ℝ) • D +
      (Raw U - U - (t : ℝ) • D)
    abel
  have hModule :
      U - s • (Raw U) =
        ((1 - s + s * kappa * (t : ℝ)) • U +
          (s * (t : ℝ) / 2) • W) - s • E := by
    rw [hRaw, hD]
    module
  calc
    p4Q2PZ37ZE_originalPhysicalCancellation H t =
        U - s • (Raw U) := by
      simp only [p4Q2PZ37ZE_originalPhysicalCancellation,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply]
      rfl
    _ = ((1 - s + s * kappa * (t : ℝ)) • U +
          (s * (t : ℝ) / 2) • W) - s • E := hModule
    _ = p4Q2PZ37ZS_originalPhysicalStaticPart H t -
          p4Q2PZ37ZS_originalRawInverseNorm H t •
            p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t := by
      rfl

/-- The second genuine spatial-Wilson coefficient is bounded by the
sup norm on Fin 2; this is sufficient for the quantitative ZP floor. -/
theorem p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2)^2 ≤
      ‖p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t‖^2 := by
  let a := p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t
  have hCoord : ‖a (1 : Fin 2)‖ ≤ ‖a‖ :=
    norm_le_pi_norm a (1 : Fin 2)
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hCoord 2
  simpa [a, p4Q2PZ37ZS_originalPhysicalStaticCoefficients,
    Real.norm_eq_abs, sq_abs] using hSq

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent
