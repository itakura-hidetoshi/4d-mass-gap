import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticTwoModePhysicalGLPositiveV5_PZ37ZN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralDetectorMatrixV5_HO
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFiniteGLSOSComplementComparisonV5_HR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZP — genuine frozen Wilson static physical GL quantitative floor

The same literal Gauss-law physical source a₀ U_H + a₁ W_H U_H from
PZ37ZN is measured by the original full-link and full-pair-Haar
two-interacting-Wilson-posterior variance-normalized GL mass.
PZ37ZN proves that mass strictly positive for every nonzero a.

This file constructs an ACTUAL real-linear two-mode GI detector at
every original spatial link and complete pair-boundary. The original
GL integral of its weighted squares is made into a genuine symmetric
bilinear form via HO's integrability/polarization construction, and
then into its exactly matching Fin 2 real Gram matrix.

The entire original Wilson GL mass is IDENTICALLY that matrix's
quadratic form for every signed a, including a=0. Continuous quadratic
homogeneity is supplied by HR's already checked pinned mathlib matrix
lemmas. On the compact real coefficient unit sphere the original
positive definite posterior mass therefore admits an unconditional
model-dependent floor

  exists m_(H,b)>0 : for every a,
    m_(H,b)*||a||² <= M_GL(H,b; a₀ U_H + a₁ W_H U_H).

This retains the exact original posterior and its true variance
denominators and only assumes frozen b>0. The constant is NOT uniform
in H, physical scale, or depth; no invented rank premise, independent
Haar posterior, compensated Q_GI/N_H floor, new axiom, sorry, admit,
native_decide, E/F/H1-H4, or continuum YM mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZP_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine static physical unit/action response, as a real
linear map of its TWO signed source coefficients, at the ACTUAL frozen
two-interacting-Wilson-posterior link and complete pair-boundary. -/
noncomputable def p4Q2PZ37ZP_originalStaticPhysicalGIDetector
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (Fin 2 → ℝ) →ₗ[ℝ] ℝ := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let G := p4Q2JH_originalGIResponseCLM H b hb e z
  let A : ℝ := G (L (1 : C(Cfg, ℝ)))
  let B : ℝ := G (L (p4Q2JI_actualSpatialWilsonContinuous H))
  exact {
    toFun := fun a => a 0 * A + a 1 * B
    map_add' := by
      intro a c
      simp only [Pi.add_apply]
      ring
    map_smul' := by
      intro c a
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
  }

/-- Exact equality of the coefficient-linear real detector and the
unchanged original physical two-Wilson-posterior GI expectation gap.
The spatial Haar-L² physical identification is already proved in ZN. -/
theorem p4Q2PZ37ZP_originalStaticPhysicalGIDetector_eq_GI
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (a : Fin 2 → ℝ) :
    p4Q2PZ37ZP_originalStaticPhysicalGIDetector H b hb e z a =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e z := by
  rw [p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow]
  unfold p4Q2PZ37ZP_originalStaticPhysicalGIDetector
  rfl

/-- GL's original signed-square/actual-variance integrability holds
on the exact physical static source at every real coefficient pair.
This discharges HO's weighted bilinear integrability premise WITHOUT
a separately assumed majorant or substitute Haar posterior. -/
theorem p4Q2PZ37ZP_originalStaticPhysicalGI_integrable
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (a : Fin 2 → ℝ) :
    Integrable
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        (p4Q2PZ37ZP_originalStaticPhysicalGIDetector H b hb.le e z a)^2 /
        p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
          H b hb.le z.2 e)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Pair := Cfg × Cfg
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  have hInt :=
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
      H b hb (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e
  apply hInt.congr
  filter_upwards with z
  rw [p4Q2PZ37ZP_originalStaticPhysicalGIDetector_eq_GI]

/-- The unchanged full-link Wilson GL variance-weighted integral
defines a real bilinear form on the authentic two-mode coefficient
space, with all integrability coming from GL, not an assumed frame. -/
noncomputable def p4Q2PZ37ZP_originalStaticPhysicalGLBilinear
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    p4Q2HO_weightedIntegralBilin
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
      (p4Q2PZ37ZP_originalStaticPhysicalGIDetector H b hb.le e)
      (fun z => p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e)
      (p4Q2PZ37ZP_originalStaticPhysicalGI_integrable H b hb e)

/-- The matrix of the ACTUAL full-link GL integral on physical
(U_H, W_H U_H), rather than a source proxy or finite-context SOS. -/
noncomputable def p4Q2PZ37ZP_originalStaticPhysicalGLMatrix
    (H : ℕ) (b : ℝ) (hb : 0 < b) : Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.BilinForm.toMatrix'
    (p4Q2PZ37ZP_originalStaticPhysicalGLBilinear H b hb)

/-- Exact original Wilson full-link GL mass equality to its true
finite real two-source posterior Gram quadratic value. -/
theorem p4Q2PZ37ZP_originalStaticPhysicalGLMatrix_quad_eq_GL
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (a : Fin 2 → ℝ) :
    star a ⬝ᵥ
        ((p4Q2PZ37ZP_originalStaticPhysicalGLMatrix H b hb) *ᵥ a) =
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Pair := Cfg × Cfg
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D := p4Q2PZ37ZP_originalStaticPhysicalGIDetector H b hb.le
  let V := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb.le
  let B := p4Q2PZ37ZP_originalStaticPhysicalGLBilinear H b hb
  calc
    star a ⬝ᵥ
        ((p4Q2PZ37ZP_originalStaticPhysicalGLMatrix H b hb) *ᵥ a) =
      B a a := p4Q2HO_realBilin_matrix_pairing B a a
    _ = p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset Link) := by
      simp only [B, p4Q2PZ37ZP_originalStaticPhysicalGLBilinear,
        LinearMap.sum_apply, p4Q2HO_weightedIntegralBilin_apply,
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass,
        p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean,
        pow_two]
      apply Finset.sum_congr rfl
      intro e _he
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ZP_originalStaticPhysicalGIDetector_eq_GI]
      ring

/-- HR's compact-sphere argument applies to the genuine static
two-mode integrated GL Gram because its quadratic form is a finite
real matrix, not merely a pointwise-positive integral. -/
theorem p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ m : ℝ, 0 < m ∧ ∀ a : Fin 2 → ℝ,
      m * ‖a‖ ^ 2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let B := p4Q2PZ37ZP_originalStaticPhysicalGLMatrix H b hb
  let q : (Fin 2 → ℝ) → ℝ := fun a =>
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hQuad (a : Fin 2 → ℝ) :
      star a ⬝ᵥ (B *ᵥ a) = q a :=
    p4Q2PZ37ZP_originalStaticPhysicalGLMatrix_quad_eq_GL H b hb a
  have hCont : Continuous q := by
    have heq : q = (fun a => star a ⬝ᵥ (B *ᵥ a)) := by
      funext a
      exact (hQuad a).symm
    rw [heq]
    exact p4Q2HR_realMatrix_quad_continuous B
  have hHom (c : ℝ) (a : Fin 2 → ℝ) :
      q (c • a) = c ^ 2 * q a := by
    calc
      q (c • a) = star (c • a) ⬝ᵥ (B *ᵥ (c • a)) := (hQuad _).symm
      _ = c ^ 2 * (star a ⬝ᵥ (B *ᵥ a)) :=
        p4Q2HR_realMatrix_quad_smul B c a
      _ = c ^ 2 * q a := by rw [hQuad]
  have hPos (a : Fin 2 → ℝ) (ha : a ≠ 0) : 0 < q a :=
    p4Q2PZ37ZN_originalStaticTwoMode_fullLinkGL_pos
      H b hb e e' left₀ right₀ a ha
  obtain ⟨m, M, hm, hM, hFloor⟩ :=
    p4Q2HR_continuous_pos_quadratic_norm_bounds q hCont hHom hPos
  refine ⟨m, hm, ?_⟩
  intro a
  exact (hFloor a).1

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZP_originalStaticPhysicalGIDetector_eq_GI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZP_originalStaticPhysicalGI_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZP_originalStaticPhysicalGLMatrix_quad_eq_GL
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
