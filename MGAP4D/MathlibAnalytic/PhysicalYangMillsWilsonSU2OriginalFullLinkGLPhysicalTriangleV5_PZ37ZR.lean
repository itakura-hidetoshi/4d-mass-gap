import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllPhysicalGLNullGIEquivalenceV5_PZ37ZM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZR — actual full-link Wilson posterior GL physical triangle

This is the exact physical instance of the quadratic weighted-detector
stability route, with NO change of sources, link variance, or interacting
original SU(2) Wilson posterior measures.

For any TWO actual Gauss-law physical Haar-L² sources f,g with genuine
continuous spatial Haar representatives, JH identifies the ORIGINAL
two-interacting-Wilson-posterior GI gap with its bounded REAL-LINEAR
Riesz response. The physical difference f-g retains the genuine
continuous representative psi_f-psi_g. Hence the unchanged original
GI(f-g) = GI(f)-GI(g) holds at each real link and full pair-boundary.

Use the ORIGINAL GL integrability, the true positive original
posterior density-row variance, and square algebra pointwise, then
integrate over the ACTUAL pair-Haar and sum ALL actual spatial links:
  M_GL(f) <= 2 M_GL(f-g) + 2 M_GL(g)
  M_GL(f-g) >= M_GL(f)/2 - M_GL(g).

The continuous-representative requirement is theorem-verified for
the Wilson static sources and the actual fine raw/normalized Wilson
transfer. No artificial test source, posterior substitution, assumed
positive frame, new axiom, sorry, admit, native_decide, volume-uniform
constant, endpoint E/F, H1-H4, or continuum Yang-Mills gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZR_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Difference linearity for exactly two authentic physical Wilson
sources with ACTUAL continuous representatives: the two distinct
interacting posterior laws and their fixed b are unchanged. -/
theorem p4Q2PZ37ZR_originalGI_sub_of_physicalContinuousRepresentatives
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (psiF psiG :
      C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
    (hf : (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiF)
    (hg : (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiG)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb (f-g) e z =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f e z -
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb g e z := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let G := p4Q2JH_originalGIResponseCLM H b hb e z
  have hSub : ((f - g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = L (psiF - psiG) := by
    change (f : Lp ℝ 2 haar) - (g : Lp ℝ 2 haar) = L (psiF - psiG)
    rw [hf, hg, map_sub]
  have hRepF : (fun A : Cfg => (f : Lp ℝ 2 haar) A) =ᵐ[haar] psiF := by
    rw [hf]
    exact psiF.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hRepG : (fun A : Cfg => (g : Lp ℝ 2 haar) A) =ᵐ[haar] psiG := by
    rw [hg]
    exact psiG.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hRepSub : (fun A : Cfg =>
      ((f - g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 haar) A) =ᵐ[haar] (psiF - psiG) := by
    rw [hSub]
    exact (psiF - psiG).coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hAgreeF := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb e z f psiF hRepF
  have hAgreeG := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb e z g psiG hRepG
  have hAgreeSub := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb e z (f-g) (psiF-psiG) hRepSub
  rw [← hAgreeSub, ← hAgreeF, ← hAgreeG]
  change G ((f - g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = G (f : Lp ℝ 2 haar) - G (g : Lp ℝ 2 haar)
  change G ((f : Lp ℝ 2 haar) - (g : Lp ℝ 2 haar)) =
    G (f : Lp ℝ 2 haar) - G (g : Lp ℝ 2 haar)
  rw [map_sub]

/-- TRUE original two-posterior full-link/whole-pair-Haar quadratic
triangle: an inequality between masses of the SAME physical
Gauss-law sources f, f-g and g, not a surrogate Q_GI density. -/
theorem p4Q2PZ37ZR_originalFullLinkGLMass_le_two_sub_add_two
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (psiF psiG :
      C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
    (hf : (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiF)
    (hg : (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiG) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
    2 * p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le (f-g)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) +
    2 * p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le g
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Pair := Cfg × Cfg
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let G := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
  let V := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb.le
  let LinkMass := p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean H b hb.le
  have hLink (e : Link) :
      LinkMass f e ≤ 2 * LinkMass (f-g) e + 2 * LinkMass g e := by
    have hIntF :=
      p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
        H b hb f e
    have hIntSub :=
      p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
        H b hb (f-g) e
    have hIntG :=
      p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
        H b hb g e
    have hRight :
        Integrable (fun z : Pair => 2 * ((G (f-g) e z)^2 / V z.2 e) +
          2 * ((G g e z)^2 / V z.2 e)) μ :=
      (hIntSub.const_mul 2).add (hIntG.const_mul 2)
    have hPoint (z : Pair) :
        (G f e z)^2 / V z.2 e ≤
          2 * ((G (f-g) e z)^2 / V z.2 e) +
          2 * ((G g e z)^2 / V z.2 e) := by
      have hLinear :=
        p4Q2PZ37ZR_originalGI_sub_of_physicalContinuousRepresentatives
          H b hb.le f g psiF psiG hf hg e z
      have hSq : (G f e z)^2 ≤
          2 * (G (f-g) e z)^2 + 2 * (G g e z)^2 := by
        dsimp [G] at hLinear ⊢
        rw [sub_eq_iff_eq_add] at hLinear
        rw [hLinear]
        nlinarith [sq_nonneg (G (f-g) e z - G g e z)]
      calc
        (G f e z)^2 / V z.2 e ≤
            (2 * (G (f-g) e z)^2 + 2 * (G g e z)^2) / V z.2 e :=
          (div_le_div_iff_of_pos_right
            (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
              H b hb z.2 e)).2 hSq
        _ = 2 * ((G (f-g) e z)^2 / V z.2 e) +
            2 * ((G g e z)^2 / V z.2 e) := by ring
    have hIntegral :
        (∫ z : Pair, (G f e z)^2 / V z.2 e ∂μ) ≤
          ∫ z : Pair,
            2 * ((G (f-g) e z)^2 / V z.2 e) +
            2 * ((G g e z)^2 / V z.2 e) ∂μ :=
      integral_mono hIntF hRight hPoint
    change (∫ z : Pair, (G f e z)^2 / V z.2 e ∂μ) ≤
      2 * (∫ z : Pair, (G (f-g) e z)^2 / V z.2 e ∂μ) +
      2 * (∫ z : Pair, (G g e z)^2 / V z.2 e ∂μ)
    calc
      _ ≤ ∫ z : Pair, 2 * ((G (f-g) e z)^2 / V z.2 e) +
          2 * ((G g e z)^2 / V z.2 e) ∂μ := hIntegral
      _ = _ := by
        rw [integral_add (hIntSub.const_mul 2) (hIntG.const_mul 2),
          integral_const_mul, integral_const_mul]
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  calc
    (∑ e : Link, LinkMass f e) ≤
        ∑ e : Link, (2 * LinkMass (f-g) e + 2 * LinkMass g e) :=
      Finset.sum_le_sum (fun e _ => hLink e)
    _ = 2 * (∑ e : Link, LinkMass (f-g) e) +
          2 * (∑ e : Link, LinkMass g e) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Physical-source lower perturbation stability, exactly for the
original all-link and entire pair-Haar two-Wilson-posterior GL mass. -/
theorem p4Q2PZ37ZR_originalFullLinkGLMass_sub_lower
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (psiF psiG :
      C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
    (hf : (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiF)
    (hg : (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ psiG) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) / 2 -
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le g
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le (f-g)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  have h := p4Q2PZ37ZR_originalFullLinkGLMass_le_two_sub_add_two
    H b hb f g psiF psiG hf hg
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZR_originalGI_sub_of_physicalContinuousRepresentatives
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZR_originalFullLinkGLMass_le_two_sub_add_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZR_originalFullLinkGLMass_sub_lower
