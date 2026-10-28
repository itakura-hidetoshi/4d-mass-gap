import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteFamilyPositiveRayleighCompactnessV5_PZ37ZY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZZ — quantitative genuine Wilson Rayleigh fine error and uniformity gate

ZW2's ORIGINAL two-interacting-Wilson-posterior full-spatial-link,
complete-pair-Haar GL bilinear form obeys the genuine physical Hilbert
bound C_(H,b) = 2 * |Links(H)| / exp(-16 b).  ZV2/ZW3 furnish the
ACTUAL fine tangent X_(H,t) = (U_H - T_t U_H)/t at t>0 and the
NONZERO genuine centered Wilson limit V_H.

An elementary positive-bilinear Rayleigh stability inequality yields
  |R_(H,b)(F_t) - R_(H,b)(V_H)|
    <= 5 C_(H,b) ||X_(H,t)-V_H|| / ||V_H||
whenever the actual tangent displacement is <= ||V_H||/2.

Together with ZX's EXACT original two-mode Gram value, an all-volume
common positive fine Rayleigh floor follows PROVIDED BOTH:
  (i)  a uniform original centered-GL Gram / physical-norm lower bound,
  (ii) a common positive fine radius controlling the ACTUAL
       normalized tangent error by its volume-dependent GL cap.

Neither condition is silently inferred from finite-family compactness.
The NEW inequality makes the unproved infinite-volume rate obstruction
quantitative, without a new posterior/source/axiom, sorry/admit/
native_decide, compensation of the disproved ZA two-context bound,
H1-H4, endpoint E/F or continuum Yang-Mills mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact elementary stability modulus for an authentic bounded
positive symmetric quadratic form on its original normed carrier.
The source norm in the denominator is NOT a coefficient norm. -/
theorem p4Q2PZ37ZZ_positiveBilinear_Rayleigh_error_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : LinearMap.BilinForm ℝ E)
    (hSym : LinearMap.IsSymm B)
    (hPos : ∀ u : E, 0 ≤ B u u)
    (C : ℝ) (hC : 0 ≤ C)
    (hUpper : ∀ u : E, B u u ≤ C * ‖u‖^2)
    (x y : E) (hy : y ≠ 0)
    (hNear : ‖x-y‖ ≤ ‖y‖ / 2) :
    |B x x / ‖x‖^2 - B y y / ‖y‖^2| ≤
      5 * C * ‖x-y‖ / ‖y‖ := by
  have hNormGap : |‖x‖ - ‖y‖| ≤ ‖x-y‖ :=
    abs_norm_sub_norm_le x y
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hXLower : ‖y‖ / 2 ≤ ‖x‖ := by
    have hh := (abs_le.mp hNormGap).1
    linarith
  have hXUpper : ‖x‖ ≤ (3 / 2 : ℝ) * ‖y‖ := by
    have hh := (abs_le.mp hNormGap).2
    linarith
  have hX : 0 < ‖x‖ := lt_of_lt_of_le (half_pos hY) hXLower
  have hXSq : 0 < ‖x‖^2 := pow_pos hX 2
  have hYSq : 0 < ‖y‖^2 := pow_pos hY 2
  have hPair (u v : E) : |B u v| ≤ C * ‖u‖ * ‖v‖ := by
    have hCS : (B u v)^2 ≤ B u u * B v v :=
      B.apply_sq_le_of_symm hPos hSym u v
    have hMul : B u u * B v v ≤
        (C * ‖u‖^2) * (C * ‖v‖^2) :=
      mul_le_mul (hUpper u) (hUpper v) (hPos v)
        (mul_nonneg hC (sq_nonneg _))
    have hSq : |B u v|^2 ≤ (C * ‖u‖ * ‖v‖)^2 := by
      calc
        |B u v|^2 = (B u v)^2 := sq_abs _
        _ ≤ B u u * B v v := hCS
        _ ≤ (C * ‖u‖^2) * (C * ‖v‖^2) := hMul
        _ = (C * ‖u‖ * ‖v‖)^2 := by ring
    have hR : 0 ≤ C * ‖u‖ * ‖v‖ := by positivity
    nlinarith [abs_nonneg (B u v)]
  have hExpand (u v : E) :
      B u u - B v v = B (u-v) u + B v (u-v) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hMassDelta :
      |B x x - B y y| ≤ C * (‖x‖+‖y‖) * ‖x-y‖ := by
    rw [hExpand]
    calc
      |B (x-y) x + B y (x-y)| ≤
          |B (x-y) x| + |B y (x-y)| := abs_add_le _ _
      _ ≤ C * ‖x-y‖ * ‖x‖ + C * ‖y‖ * ‖x-y‖ :=
        add_le_add (hPair (x-y) x) (hPair y (x-y))
      _ = C * (‖x‖+‖y‖) * ‖x-y‖ := by ring
  have hNormSqDelta :
      |‖y‖^2 - ‖x‖^2| ≤ (‖x‖+‖y‖) * ‖x-y‖ := by
    have hReverse : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
      rw [abs_sub_comm]
      exact hNormGap
    have hFactor : ‖y‖^2 - ‖x‖^2 =
        (‖y‖-‖x‖) * (‖y‖+‖x‖) := by ring
    rw [hFactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖y‖+‖x‖)]
    calc
      |‖y‖-‖x‖| * (‖y‖+‖x‖) ≤
          ‖x-y‖ * (‖y‖+‖x‖) :=
        mul_le_mul_of_nonneg_right hReverse (by positivity)
      _ = (‖x‖+‖y‖) * ‖x-y‖ := by ring
  have hRayleighCap : |B x x / ‖x‖^2| ≤ C := by
    rw [abs_of_nonneg (div_nonneg (hPos x) hXSq.le)]
    exact (div_le_iff₀ hXSq).2 (hUpper x)
  have hTerm1 :
      |(B x x-B y y)/‖y‖^2| ≤
        (C*(‖x‖+‖y‖)*‖x-y‖)/‖y‖^2 := by
    rw [abs_div, abs_of_pos hYSq]
    exact div_le_div_of_nonneg_right hMassDelta hYSq.le
  have hTerm2 :
      |(B x x/‖x‖^2) * ((‖y‖^2-‖x‖^2)/‖y‖^2)| ≤
        C * (((‖x‖+‖y‖)*‖x-y‖)/‖y‖^2) := by
    have hAbsRight :
        |(‖y‖^2-‖x‖^2)/‖y‖^2| =
          |‖y‖^2-‖x‖^2| / ‖y‖^2 := by
      rw [abs_div, abs_of_pos hYSq]
    rw [abs_mul, hAbsRight]
    exact mul_le_mul hRayleighCap
      (div_le_div_of_nonneg_right hNormSqDelta hYSq.le)
      (div_nonneg (abs_nonneg _) hYSq.le) hC
  have hIdentity :
      B x x/‖x‖^2 - B y y/‖y‖^2 =
        (B x x-B y y)/‖y‖^2 +
          (B x x/‖x‖^2) * ((‖y‖^2-‖x‖^2)/‖y‖^2) := by
    field_simp [ne_of_gt hXSq, ne_of_gt hYSq]
    ring
  have hSumBound : 2 * (‖x‖+‖y‖) ≤ 5 * ‖y‖ := by
    linarith
  have hCD : 0 ≤ C * ‖x-y‖ := mul_nonneg hC (norm_nonneg _)
  calc
    |B x x/‖x‖^2 - B y y/‖y‖^2| =
        |(B x x-B y y)/‖y‖^2 +
          (B x x/‖x‖^2)*((‖y‖^2-‖x‖^2)/‖y‖^2)| := by
      rw [hIdentity]
    _ ≤ |(B x x-B y y)/‖y‖^2| +
          |(B x x/‖x‖^2)*((‖y‖^2-‖x‖^2)/‖y‖^2)| :=
      abs_add_le _ _
    _ ≤ (C*(‖x‖+‖y‖)*‖x-y‖)/‖y‖^2 +
          C*(((‖x‖+‖y‖)*‖x-y‖)/‖y‖^2) :=
      add_le_add hTerm1 hTerm2
    _ = (2*C*(‖x‖+‖y‖)*‖x-y‖)/‖y‖^2 := by ring
    _ ≤ (5*C*‖y‖*‖x-y‖)/‖y‖^2 := by
      apply div_le_div_of_nonneg_right _ hYSq.le
      have hh := mul_le_mul_of_nonneg_right hSumBound hCD
      nlinarith only [hh]
    _ = 5*C*‖x-y‖/‖y‖ := by
      field_simp [ne_of_gt hY]
      ring

local instance p4Q2PZ37ZZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZZ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ACTUAL original normalized physical fine tangent displacement,
in the unchanged Gauss-law Hilbert metric and continuous Haar carrier. -/
noncomputable def p4Q2PZ37ZZ_originalTangentDisplacement
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  ‖p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t -
    p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖

/-- Quantitative Rayleigh error on the TRUE Wilson transfer F_t,
with the unchanged genuine full-link interacting-posterior GL form.
The finite-volume-dependent cap is EXPLICIT. -/
theorem p4Q2PZ37ZZ_originalPositiveFine_RayleighError_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (hNear : p4Q2PZ37ZZ_originalTangentDisplacement H t ≤
        ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ / 2) :
    |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| ≤
      5 * p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
        p4Q2PZ37ZZ_originalTangentDisplacement H t /
          ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ := by
  let E := p4Q2PZ37ZW2_originalContinuousPhysicalSources H
  let B := p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb
  let C := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  let x : E := p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t
  let y : E := p4Q2PZ37ZW3_originalCenteredPhysicalLift H
  have hSym : LinearMap.IsSymm B := by
    refine ⟨?_⟩
    intro u v
    simpa only [RingHom.id_apply] using
      p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_symm H b hb u v
  have hPos (u : E) : 0 ≤ B u u := by
    rw [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL]
    exact p4Q2PZ37ZG_originalGL_fullLink_nonneg H b hb u
  have hC : 0 ≤ C := by
    dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
    positivity
  have hUpper (u : E) : B u u ≤ C * ‖u‖^2 := by
    rw [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL]
    have hh := p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
      H b hb
      (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    calc
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
          ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            (2 * ‖(u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖^2)) /
            Real.exp (-16*b) := hh
      _ = C * ‖u‖^2 := by
        change
          ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            (2 * ‖u‖^2)) / Real.exp (-16*b) =
          (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
            Real.exp (-16*b)) * ‖u‖^2
        ring
  have hy : y ≠ 0 := by
    intro hh
    apply p4Q2PZ37ZW_originalCenteredDirection_ne_zero H
    have h := congrArg (fun z : E =>
      (z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) hh
    simpa only [y, p4Q2PZ37ZW3_originalCenteredPhysicalLift, Submodule.coe_zero] using h
  have hPointwise :
      |B x x / ‖x‖^2 - B y y / ‖y‖^2| ≤
        5 * C * ‖x-y‖ / ‖y‖ :=
    p4Q2PZ37ZZ_positiveBilinear_Rayleigh_error_le
      B hSym hPos C hC hUpper x y hy hNear
  rw [p4Q2PZ37ZW3_originalPositiveFine_Rayleigh_eq_tangent H b hb t ht]
  unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
  change
    |p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) / ‖x‖^2 -
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) / ‖y‖^2| ≤
      5*C*‖x-y‖/‖y‖
  rw [← p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL H b hb x,
    ← p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL H b hb y]
  exact hPointwise

/-- Explicit ALL-volume sufficiency gate: a shared original centered
Gram coercivity bound AND a common fine tangent-rate estimate, measured
against each true physical Wilson source norm and original GL cap,
give a single positive fine interval and physical Rayleigh floor.
These two estimates are HYPOTHESES, NOT established all-volume facts. -/
theorem p4Q2PZ37ZZ_originalAllVolumes_quantitativeUniformFineGate
    (b : ℕ → ℝ) (hb : ∀ H : ℕ, 0 < b H)
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hGram : ∀ H : ℕ,
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H))
    (hNear : ∀ (H : ℕ) (t : Set.Ici (0 : ℝ)),
      0 < (t : ℝ) → (t : ℝ) < ρ →
      p4Q2PZ37ZZ_originalTangentDisplacement H t ≤
        ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ / 2)
    (hError : ∀ (H : ℕ) (t : Set.Ici (0 : ℝ)),
      0 < (t : ℝ) → (t : ℝ) < ρ →
      5 * p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H (b H) *
        p4Q2PZ37ZZ_originalTangentDisplacement H t ≤
          (c / 2) * ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖) :
    0 < ρ ∧ ∀ (H : ℕ) (t : Set.Ici (0 : ℝ)),
      0 < (t : ℝ) → (t : ℝ) < ρ →
        c / 2 ≤
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
            H (b H) (hb H) (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  refine ⟨hρ, ?_⟩
  intro H t ht htρ
  have hNorm :
      0 < ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ := by
    apply norm_pos_iff.mpr
    intro hv
    apply p4Q2PZ37ZW_originalCenteredDirection_ne_zero H
    have hh := congrArg (fun z :
      p4Q2PZ37ZW2_originalContinuousPhysicalSources H =>
      (z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) hv
    simpa only [p4Q2PZ37ZW3_originalCenteredPhysicalLift, Submodule.coe_zero] using hh
  have hAtLimit : c ≤
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H) (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) :=
    ((p4Q2PZ37ZX_uniformCenteredRayleigh_iff_originalGram b hb c).2 hGram) H
  have hDeviation :=
    p4Q2PZ37ZZ_originalPositiveFine_RayleighError_le
      H (b H) (hb H) t ht (hNear H t ht htρ)
  have hSmall :
      5 * p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H (b H) *
          p4Q2PZ37ZZ_originalTangentDisplacement H t /
            ‖p4Q2PZ37ZW3_originalCenteredPhysicalLift H‖ ≤ c/2 :=
    (div_le_iff₀ hNorm).2 (hError H t ht htρ)
  have hGap := (abs_le.mp (hDeviation.trans hSmall)).1
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ZZ_positiveBilinear_Rayleigh_error_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZZ_originalPositiveFine_RayleighError_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZZ_originalAllVolumes_quantitativeUniformFineGate
