import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCenteredFineTangentV5_PZ37ZV2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticPhysicalGLQuantitativeV5_PZ37ZP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZW — exact centered physical tangent, genuine GL positivity

Work in the original Gauss-law physical Hilbert space and with the
unchanged two interacting Wilson posteriors, the complete pair-Haar
boundary integral, and all actual spatial links. The strong tangent
from ZV is the literally centered spatial Wilson physical source.
Its true coefficient in the spatial Wilson direction is 1/2, so
the original two-mode ZN full-link GL positivity applies.

The numerator is strictly positive at frozen b>0, and the tangent
itself is nonzero by the original nonconstant Wilson action (IY).
Consequently its genuine source-normalized GL Rayleigh value is
strictly positive. There is no new physical/posterior surrogate,
new axiom, sorry/admit/native_decide, volume-uniform estimate,
endpoint E/F, H1-H4, or continuum mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZW_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual ZV strong fine-tangent source, with no normalization
derivative or arbitrary endpoint convention. -/
noncomputable def p4Q2PZ37ZW_originalCenteredPhysicalDirection
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  (1 / 2 : ℝ) •
    (p4Q2JU_originalSpatialWilsonPhysicalSource H -
      (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)

/-- The true Wilson two-mode coefficients of the ZV tangent. -/
noncomputable def p4Q2PZ37ZW_originalCenteredCoefficients
    (H : ℕ) : Fin 2 → ℝ :=
  fun i => if i = 0 then
    -(1 / 2 : ℝ) *
      inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  else (1 / 2 : ℝ)

theorem p4Q2PZ37ZW_originalCenteredCoefficients_one
    (H : ℕ) :
    p4Q2PZ37ZW_originalCenteredCoefficients H (1 : Fin 2) =
      (1 / 2 : ℝ) := by
  simp [p4Q2PZ37ZW_originalCenteredCoefficients]

theorem p4Q2PZ37ZW_originalCenteredCoefficients_ne_zero
    (H : ℕ) :
    p4Q2PZ37ZW_originalCenteredCoefficients H ≠ 0 := by
  intro h
  have hOne := congrArg (fun a : Fin 2 → ℝ => a (1 : Fin 2)) h
  rw [p4Q2PZ37ZW_originalCenteredCoefficients_one] at hOne
  norm_num at hOne

/-- Identification with the original TWO physical sources U_H and W_H.
The Wilson coordinate is literally 1/2, independent of the mean. -/
theorem p4Q2PZ37ZW_originalCenteredDirection_eq_static
    (H : ℕ) :
    p4Q2PZ37ZW_originalCenteredPhysicalDirection H =
      p4Q2PZ37ZN_originalStaticPhysicalSource H
        (p4Q2PZ37ZW_originalCenteredCoefficients H) := by
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let w : ℝ := inner ℝ W U
  change (1 / 2 : ℝ) • (W - w • U) =
    (-(1 / 2 : ℝ) * w) • U + (1 / 2 : ℝ) • W
  module

/-- The original two-mode physical Gram floor gives a STRICTLY positive
full-link, complete-pair-Haar mass of the true centered tangent. -/
theorem p4Q2PZ37ZW_originalCenteredDirection_GLMass_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  rw [p4Q2PZ37ZW_originalCenteredDirection_eq_static]
  exact p4Q2PZ37ZN_originalStaticTwoMode_fullLinkGL_pos
    H b hb e e' left₀ right₀
    (p4Q2PZ37ZW_originalCenteredCoefficients H)
    (p4Q2PZ37ZW_originalCenteredCoefficients_ne_zero H)

/-- The continuous ORIGINAL spatial Wilson action minus ANY constant
cannot vanish in the physical Haar-L2 carrier: this is IY's literal
nonconstant Wilson configuration argument, not a positivity premise. -/
private theorem p4Q2PZ37ZW_originalCenteredWilsonLp_ne_zero
    (H : ℕ) (c : ℝ) :
    ContinuousMap.toLp 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
      (p4Q2JI_actualSpatialWilsonContinuous H -
        c • (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))) ≠
      0 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let W := p4Q2JI_actualSpatialWilsonContinuous H
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  intro h
  have hCont : W - c • (1 : C(Cfg, ℝ)) = 0 := by
    apply (ContinuousMap.toLp_injective (p := 2) (μ := haar) (𝕜 := ℝ))
    simpa only [map_zero] using h
  obtain ⟨B₀, B₁, hW⟩ := p4Q2IY_originalSpatialWilsonAction_not_constant H
  have hc (B : Cfg) : W B = c := by
    have hc' : W = c • (1 : C(Cfg, ℝ)) := sub_eq_zero.mp hCont
    have hs := congrArg (fun f : C(Cfg, ℝ) => f B) hc'
    simpa using hs
  exact hW ((hc B₀).trans (hc B₁).symm)

/-- The physical Hilbert tangent has nonzero source norm. This
conclusion is separate from GL source detection. -/
theorem p4Q2PZ37ZW_originalCenteredDirection_ne_zero
    (H : ℕ) :
    p4Q2PZ37ZW_originalCenteredPhysicalDirection H ≠ 0 := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let w : ℝ := inner ℝ W U
  intro h
  have hZero : W - w • U = 0 := by
    have hh : (1 / 2 : ℝ) • (W - w • U) = 0 := h
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have hRep :
      ((W - w • U : Phys) : Lp ℝ 2 haar) =
        L (p4Q2JI_actualSpatialWilsonContinuous H - w • (1 : C(Cfg, ℝ))) := by
    rw [Submodule.coe_sub, Submodule.coe_smul,
      p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
      p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
      map_sub, map_smul]
  have hLpZero :
      L (p4Q2JI_actualSpatialWilsonContinuous H - w • (1 : C(Cfg, ℝ))) =
        0 := by
    rw [← hRep, hZero]
    rfl
  exact p4Q2PZ37ZW_originalCenteredWilsonLp_ne_zero H w hLpZero

/-- This is the genuine RAYLEIGH value at the ZV strong tangent,
not a surrogate Gram quotient. The denominator is strictly positive. -/
theorem p4Q2PZ37ZW_originalCenteredDirection_Rayleigh_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
  unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
  exact div_pos
    (p4Q2PZ37ZW_originalCenteredDirection_GLMass_pos
      H b hb e e' left₀ right₀)
    (pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2)

/-- The proven ZV genuine normalized Wilson tangent converges strongly
to exactly the same physical direction whose Rayleigh is positive. -/
theorem p4Q2PZ37ZW_originalFullPhysicalTangent_tendsto_centered
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)) := by
  exact p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_tendsto H

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalCenteredCoefficients_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalCenteredDirection_eq_static
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalCenteredDirection_GLMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalCenteredDirection_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalCenteredDirection_Rayleigh_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW_originalFullPhysicalTangent_tendsto_centered
