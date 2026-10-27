import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCenteredGLRayleighLimitV5_PZ37ZW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZW2 — genuine full-link GL quadratic continuity

The original interacting Wilson signed GI response agrees with a real
bounded Riesz functional on every genuine Gauss-law Haar-L2 source
admitting a continuous representative (JH). These sources form a
linear submodule of the unchanged physical Hilbert space.

By polarization, HO constructs the original GL all-link complete
pair-Haar integral as a symmetric positive semidefinite real bilinear
form on that physical source submodule, with its diagonal IDENTICALLY
the original source mass. ZC bounds this diagonal by the original
physical norm and explicit finite link count. The Cauchy-Schwarz
inequality for positive forms then implies Hilbert-norm continuity.

This is continuity of the ACTUAL mass on actual continuous-represented
physical sources, not a new posterior, frame assumption, or arbitrary
extension of JH's representative agreement to every Lp function.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A real nonnegative symmetric bilinear form whose diagonal has a
quadratic norm bound has a continuous quadratic value. -/
theorem p4Q2PZ37ZW2_bounded_positive_bilinear_quadratic_continuous
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E)
    (hSym : LinearMap.IsSymm B)
    (hPos : ∀ x : E, 0 ≤ B x x)
    (C : ℝ) (hC : 0 ≤ C)
    (hUpper : ∀ x : E, B x x ≤ C * ‖x‖^2) :
    Continuous (fun x : E => B x x) := by
  have hPair (x y : E) : |B x y| ≤ C * ‖x‖ * ‖y‖ := by
    have hCS : (B x y)^2 ≤ B x x * B y y :=
      B.apply_sq_le_of_symm hPos hSym x y
    have hMul : B x x * B y y ≤
        (C * ‖x‖^2) * (C * ‖y‖^2) :=
      mul_le_mul (hUpper x) (hUpper y) (hPos y)
        (mul_nonneg hC (sq_nonneg _))
    have hSq : |B x y|^2 ≤ (C * ‖x‖ * ‖y‖)^2 := by
      calc
        |B x y|^2 = (B x y)^2 := sq_abs _
        _ ≤ B x x * B y y := hCS
        _ ≤ (C * ‖x‖^2) * (C * ‖y‖^2) := hMul
        _ = (C * ‖x‖ * ‖y‖)^2 := by ring
    have hR : 0 ≤ C * ‖x‖ * ‖y‖ := by positivity
    nlinarith [abs_nonneg (B x y)]
  have hExpand (x y : E) :
      B x x - B y y = B (x-y) x + B y (x-y) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hDelta (x y : E) :
      |B x x - B y y| ≤ C * (‖x‖+‖y‖) * ‖x-y‖ := by
    rw [hExpand]
    calc
      |B (x-y) x + B y (x-y)| ≤
          |B (x-y) x| + |B y (x-y)| := abs_add_le _ _
      _ ≤ C * ‖x-y‖ * ‖x‖ + C * ‖y‖ * ‖x-y‖ :=
        add_le_add (hPair (x-y) x) (hPair y (x-y))
      _ = C * (‖x‖+‖y‖) * ‖x-y‖ := by ring
  rw [continuous_iff_continuousAt]
  intro y
  have hNorm :
      Tendsto (fun x : E => ‖x‖) (𝓝 y) (𝓝 ‖y‖) :=
    continuous_norm.continuousAt
  have hSub :
      Tendsto (fun x : E => ‖x-y‖) (𝓝 y) (𝓝 (0 : ℝ)) := by
    have hh : ContinuousAt (fun x : E => ‖x-y‖) y :=
      (continuous_id.sub continuous_const).norm.continuousAt
    simpa only [ContinuousAt, sub_self, norm_zero, id_eq] using hh
  have hProd :
      Tendsto (fun x : E => C * (‖x‖+‖y‖) * ‖x-y‖)
        (𝓝 y) (𝓝 (0 : ℝ)) := by
    have hFirst :
        Tendsto (fun x : E => C * (‖x‖+‖y‖)) (𝓝 y)
          (𝓝 (C * (‖y‖+‖y‖))) :=
      (hNorm.add_const ‖y‖).const_mul C
    simpa using hFirst.mul hSub
  have hAbs :
      Tendsto (fun x : E => |B x x - B y y|) (𝓝 y) (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hProd
      (Filter.Eventually.of_forall (fun x : E => abs_nonneg (B x x-B y y)))
      (Filter.Eventually.of_forall (fun x : E => hDelta x y))
  change Tendsto (fun x : E => B x x) (𝓝 y) (𝓝 (B y y))
  rw [Metric.tendsto_nhds] at hAbs ⊢
  intro eps heps
  filter_upwards [hAbs eps heps] with x hx
  simpa [Real.dist_eq, abs_abs] using hx

local instance p4Q2PZ37ZW2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZW2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZW2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZW2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZW2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZW2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Genuine physical Haar-L2 sources with a continuous reference-Haar
representative. Physical Gauss-law input is NOT replaced by a full Lp
or independent posterior. -/
noncomputable def p4Q2PZ37ZW2_originalContinuousPhysicalSources
    (H : ℕ) :
    Submodule ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) where
  carrier := {f | ∃ ψ :
      C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ),
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ ψ}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro f g ⟨ψf, hf⟩ ⟨ψg, hg⟩
    refine ⟨ψf+ψg, ?_⟩
    change
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) +
      (g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ (ψf+ψg)
    rw [hf, hg, map_add]
  smul_mem' := by
    intro c f ⟨ψf, hf⟩
    refine ⟨c • ψf, ?_⟩
    change c •
      (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ (c • ψf)
    rw [hf, map_smul]

/-- Real-linear original JH detector restricted along the TWO genuine
physical source inclusions into the original spatial Haar-L2. -/
noncomputable def p4Q2PZ37ZW2_originalGIContinuousSourceDetector
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (p4Q2PZ37ZW2_originalContinuousPhysicalSources H) →ₗ[ℝ] ℝ :=
  (p4Q2JH_originalGIResponseCLM H b hb.le e z).toLinearMap.comp
    ((Submodule.subtype
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)).comp
      (Submodule.subtype (p4Q2PZ37ZW2_originalContinuousPhysicalSources H)))

/-- No proxy: the restricted real detector equals the ACTUAL original
interacting two-posterior source expectation gap at each pair-boundary. -/
theorem p4Q2PZ37ZW2_originalGIContinuousSourceDetector_eq_originalGI
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    p4Q2PZ37ZW2_originalGIContinuousSourceDetector H b hb e z f =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        e z := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  obtain ⟨ψ, hψ⟩ := f.property
  have hRep :
      (fun A : Cfg =>
        (((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
            Lp ℝ 2 haar) A)) =ᵐ[haar] ψ := by
    rw [hψ]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  change p4Q2JH_originalGIResponseCLM H b hb.le e z
    ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = _
  exact p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb.le e z f ψ hRep

/-- Integrability supplied by ORIGINAL GL on each actual physical
source, with no artificial majorant for the weighted source response. -/
theorem p4Q2PZ37ZW2_originalGIContinuousSourceDetector_integrable
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    Integrable (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      (p4Q2PZ37ZW2_originalGIContinuousSourceDetector H b hb e z f)^2 /
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb.le z.2 e)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  have hInt :=
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
      H b hb
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) e
  apply hInt.congr
  filter_upwards with z
  rw [← p4Q2PZ37ZW2_originalGIContinuousSourceDetector_eq_originalGI H b hb e z f]

/-- Original full-link complete-pair-Haar real bilinear GL form on
the linear (not assumed complete) continuous-represented physical
source submodule. -/
noncomputable def p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    LinearMap.BilinForm ℝ (p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    p4Q2HO_weightedIntegralBilin
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
      (p4Q2PZ37ZW2_originalGIContinuousSourceDetector H b hb e)
      (fun z => p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e)
      (p4Q2PZ37ZW2_originalGIContinuousSourceDetector_integrable H b hb e)

/-- Exactly the unchanged full-link original GL source mass, including
all interacting posterior rows and their actual variance denominators. -/
theorem p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb f f =
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  simp only [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear,
    LinearMap.sum_apply, p4Q2HO_weightedIntegralBilin_apply,
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass,
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean]
  apply Finset.sum_congr rfl
  intro e _he
  apply integral_congr_ae
  filter_upwards with z
  rw [p4Q2PZ37ZW2_originalGIContinuousSourceDetector_eq_originalGI H b hb e z f]
  ring

/-- Original Haar integral is symmetric, not a new ungrounded
symmetric model. -/
theorem p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_symm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f g : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb f g =
      p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb g f := by
  classical
  simp only [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear,
    LinearMap.sum_apply, p4Q2HO_weightedIntegralBilin_apply]
  apply Finset.sum_congr rfl
  intro e _he
  apply integral_congr_ae
  filter_upwards with z
  ring

/-- The original physical GL mass is Hilbert-norm continuous on
continuous-represented genuine sources, by ZC's global upper bound
and weighted-integral Cauchy-Schwarz. -/
theorem p4Q2PZ37ZW2_originalFullLinkGLPhysicalMass_continuous
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    Continuous (fun f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H =>
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) := by
  let E := p4Q2PZ37ZW2_originalContinuousPhysicalSources H
  let B := p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb
  let C := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  have hSym : LinearMap.IsSymm B := by
    refine ⟨?_⟩
    intro f g
    simpa only [RingHom.id_apply] using
      p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_symm H b hb f g
  have hPos (f : E) : 0 ≤ B f f := by
    rw [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL]
    exact p4Q2PZ37ZG_originalGL_fullLink_nonneg H b hb f
  have hC : 0 ≤ C := by
    dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
    positivity
  have hUpper (f : E) : B f f ≤ C * ‖f‖^2 := by
    rw [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL]
    have hh := p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
      H b hb
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    calc
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
          (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (2 * ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖^2)) /
          Real.exp (-16*b) := hh
      _ = C * ‖f‖^2 := by
        change
          ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            (2 * ‖f‖^2)) / Real.exp (-16*b) =
          (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
            Real.exp (-16*b)) * ‖f‖^2
        ring
  have hCont :
      Continuous (fun f : E => B f f) :=
    p4Q2PZ37ZW2_bounded_positive_bilinear_quadratic_continuous
      B hSym hPos C hC hUpper
  have hEq : (fun f : E =>
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) =
      (fun f : E => B f f) := by
    funext f
    exact (p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL
      H b hb f).symm
  rw [hEq]
  exact hCont

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ZW2_bounded_positive_bilinear_quadratic_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW2_originalGIContinuousSourceDetector_eq_originalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW2_originalGIContinuousSourceDetector_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW2_originalFullLinkGLPhysicalMass_continuous
