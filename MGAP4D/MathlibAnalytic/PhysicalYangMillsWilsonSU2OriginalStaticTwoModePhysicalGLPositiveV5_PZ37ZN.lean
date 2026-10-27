import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllPhysicalGLNullGIEquivalenceV5_PZ37ZM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZN — true static Wilson two-source physical GL positivity

PZ37ZL proved genuine two-context posterior GI SOS positivity on the
literal static physical SU(2) Wilson (unit, spatial action) directions.
PZ37ZM proved that ONE genuine nonzero original GI response implies a
strictly positive original full-link, full-pair-Haar posterior GL mass
for an arbitrary actual Gauss-law physical source.

This module constructs the exact signed physical source
  a0 * U_H + a1 * W_H U_H
in the true gauge-invariant Haar-L², identifies its honest continuous
product-Haar representative, and uses JH's original physical GI/Riesz
agreement to transport the ZL nonzero static two-context detector
without introducing synthetic response measures.

It proves that the UNMODIFIED full-link Wilson GL mass is strictly
positive on every nonzero real coefficient pair of the original
physical static unit/Wilson-action sources. It is the fixed-source
positive-definiteness bridge toward a quantitative finite-volume
Rayleigh floor, not a quantitative lower floor itself; no fine
uniformity, artificial source, independent-Haar posterior,
compensated Q_GI/N_H bound, new axiom, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZN_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine original Gauss-law physical two-source plane. Both
basis sources are actual spatial SU(2) Wilson observables. -/
noncomputable def p4Q2PZ37ZN_originalStaticPhysicalSource
    (H : ℕ) (a : Fin 2 → ℝ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  a 0 • periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 +
    a 1 • p4Q2JU_originalSpatialWilsonPhysicalSource H

/-- This is the ACTUAL physical source in the original Haar L²,
not an independently selected continuous function. -/
theorem p4Q2PZ37ZN_originalStaticPhysicalSource_coe_eq_toLp
    (H : ℕ) (a : Fin 2 → ℝ) :
    ((p4Q2PZ37ZN_originalStaticPhysicalSource H a :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
    ContinuousMap.toLp 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (a 0 • (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ)) +
          a 1 • p4Q2JI_actualSpatialWilsonContinuous H) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  change ((a 0 • U + a 1 • W :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = L (a 0 • (1 : C(Cfg, ℝ)) +
          a 1 • p4Q2JI_actualSpatialWilsonContinuous H)
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
    map_add, map_smul, map_smul]

/-- Original two-posterior GI response on the literal signed physical
static Wilson source equals the same bounded frozen JH detector
evaluated on the two actual Haar L² directions. -/
theorem p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (a : Fin 2 → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e z =
      a 0 * p4Q2JH_originalGIResponseCLM H b hb e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))) +
      a 1 * p4Q2JH_originalGIResponseCLM H b hb e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (p4Q2JI_actualSpatialWilsonContinuous H)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let f := p4Q2PZ37ZN_originalStaticPhysicalSource H a
  let ψ : C(Cfg, ℝ) :=
    a 0 • (1 : C(Cfg, ℝ)) + a 1 • p4Q2JI_actualSpatialWilsonContinuous H
  have hf : (f : Lp ℝ 2 haar) = L ψ :=
    p4Q2PZ37ZN_originalStaticPhysicalSource_coe_eq_toLp H a
  have hRep : (fun B : Cfg => (f : Lp ℝ 2 haar) B) =ᵐ[haar] ψ := by
    rw [hf]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hAgree :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H b hb e z f ψ hRep
  rw [hf] at hAgree
  rw [← hAgree]
  change
    p4Q2JH_originalGIResponseCLM H b hb e z (L ψ) =
      a 0 * p4Q2JH_originalGIResponseCLM H b hb e z
        (L (1 : C(Cfg, ℝ))) +
      a 1 * p4Q2JH_originalGIResponseCLM H b hb e z
        (L (p4Q2JI_actualSpatialWilsonContinuous H))
  dsimp [ψ]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

/-- At fixed finite H and frozen Wilson coupling b>0,
the ORIGINAL full-link pair-Haar two-interacting-posterior GL mass
is positive for every nonzero real pair of physical static
unit/Wilson-action source coefficients. -/
theorem p4Q2PZ37ZN_originalStaticTwoMode_fullLinkGL_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (a : Fin 2 → ℝ) (ha : a ≠ 0) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  obtain ⟨z, z', c, hc, hFloor⟩ :=
    p4Q2PZ37ZL_originalStaticTwoModeGISOS_exists_positive_floor
      H b hb e e' left₀ right₀
  have hNorm : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have hSOS :
      0 < p4Q2PZ37ZL_originalStaticTwoModeGISOS H b hb.le e e' z z' a :=
    lt_of_lt_of_le (mul_pos hc hNorm) (hFloor a)
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let G := p4Q2JH_originalGIResponseCLM H b hb.le
  let u := L (1 : C(Cfg, ℝ))
  let w := L (p4Q2JI_actualSpatialWilsonContinuous H)
  have hDetect :
      (a 0 * G e z u + a 1 * G e z w ≠ 0) ∨
      (a 0 * G e' z' u + a 1 * G e' z' w ≠ 0) := by
    by_contra hNo
    have h0 : a 0 * G e z u + a 1 * G e z w = 0 := by
      by_contra hx
      exact hNo (Or.inl hx)
    have h1 : a 0 * G e' z' u + a 1 * G e' z' w = 0 := by
      by_contra hy
      exact hNo (Or.inr hy)
    have hZero :
        p4Q2PZ37ZL_originalStaticTwoModeGISOS
          H b hb.le e e' z z' a = 0 := by
      change
        (a 0 * G e z u + a 1 * G e z w)^2 +
          (a 0 * G e' z' u + a 1 * G e' z' w)^2 = 0
      rw [h0, h1]
      ring
    exact (ne_of_gt hSOS) hZero
  rcases hDetect with hDetect | hDetect
  · have hGI :
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e z ≠ 0 := by
      rw [p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow]
      exact hDetect
    exact p4Q2PZ37ZM_originalFullLinkGLMass_pos_of_originalGI_point
      H b hb (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e z hGI
  · have hGI :
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e' z' ≠ 0 := by
      rw [p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow]
      exact hDetect
    exact p4Q2PZ37ZM_originalFullLinkGLMass_pos_of_originalGI_point
      H b hb (p4Q2PZ37ZN_originalStaticPhysicalSource H a) e' z' hGI

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZN_originalStaticPhysicalSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZN_originalStaticTwoMode_fullLinkGL_pos
