import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCancellationLinearFineLowerV5_PZ37ZK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFiniteGLSOSComplementComparisonV5_HR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZL — unconditional fixed-H original static two-mode GI SOS floor

The inputs are the actual original SU(2) Wilson frozen-b two-interacting-
posterior bounded GI functionals of JH, acting on the ORIGINAL product-
Haar L² images of the Gauss-law constant unit and true spatial Wilson
action. LM proves a NONZERO determinant at two actual physical boundary
contexts, for every finite H, every b>0, and every chosen pair of links.

We construct their literal two-row signed source detector square sum,
then use that authentic nonzero determinant and the already proved HR
compact-sphere lemma to establish a positive finite-dimensional norm
floor on ALL real coefficients of (unit, spatial Wilson action).

This is a genuine static two-mode detector estimate, NOT YET the
full-link posterior pair-Haar GL mass floor for F_t. The next obligation
is to promote this original point-context floor to the original
weighted pair-Haar integral via HI joint continuity/full support,
then use JF Taylor and the ZC global GL upper bound. No assumed
frame, independent-Haar posterior, compensated Q_GI/N_H, volume-
uniformity, operator-norm differentiability, new axiom, sorry,
admit, native_decide, endpoint E/F, H1-H4, or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Exact original two-interacting-Wilson-posterior GI squared receiver
on the two ACTUAL spatial Haar-L² physical source directions:
constant unit and spatial Wilson action. The two contextual GI rows
remain distinct; no determinant compensation or plaquette averaging. -/
noncomputable def p4Q2PZ37ZL_originalStaticTwoModeGISOS
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (a : Fin 2 → ℝ) : ℝ :=
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let G := p4Q2JH_originalGIResponseCLM H b hb
  let u := L (1 : C(Cfg, ℝ))
  let w := L (p4Q2JI_actualSpatialWilsonContinuous H)
  (a 0 * G e z u + a 1 * G e z w) ^ 2 +
    (a 0 * G e' z' u + a 1 * G e' z' w) ^ 2

/-- The theorem-proved LM genuine two-context Wilson spatial minor
makes the static two-mode source GI receiver square-sum uniformly
positive on the REAL coefficient sphere for fixed finite H,b.
The coefficient norm floor is not volume-uniform and is NOT the
unproved full-link GL physical-source mass floor. -/
theorem p4Q2PZ37ZL_originalStaticTwoModeGISOS_exists_positive_floor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ∃ c : ℝ, 0 < c ∧
        ∀ a : Fin 2 → ℝ, c * ‖a‖ ^ 2 ≤
          p4Q2PZ37ZL_originalStaticTwoModeGISOS H b hb.le e e' z z' a := by
  obtain ⟨z, z', hMinor⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let G := p4Q2JH_originalGIResponseCLM H b hb.le
  let u := L (1 : C(Cfg, ℝ))
  let w := L (p4Q2JI_actualSpatialWilsonContinuous H)
  let A : ℝ := G e z u
  let B : ℝ := G e z w
  let C : ℝ := G e' z' u
  let D : ℝ := G e' z' w
  have hDet : A * D - B * C ≠ 0 := by
    change p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' ≠ 0
    exact hMinor
  let q : (Fin 2 → ℝ) → ℝ := fun a =>
    (A * a 0 + B * a 1) ^ 2 + (C * a 0 + D * a 1) ^ 2
  have hCont : Continuous q := by
    dsimp [q]
    fun_prop
  have hHom (r : ℝ) (a : Fin 2 → ℝ) :
      q (r • a) = r ^ 2 * q a := by
    dsimp [q]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hDetected (a : Fin 2 → ℝ) (ha : a ≠ 0) :
      (A * a 0 + B * a 1 ≠ 0) ∨
      (C * a 0 + D * a 1 ≠ 0) := by
    by_contra hNo
    have hR1 : A * a 0 + B * a 1 = 0 := by
      by_contra hx
      exact hNo (Or.inl hx)
    have hR2 : C * a 0 + D * a 1 = 0 := by
      by_contra hy
      exact hNo (Or.inr hy)
    have hAMul : a 0 * (A * D - B * C) = 0 := by
      calc
        a 0 * (A * D - B * C) =
            (A * a 0 + B * a 1) * D -
              (C * a 0 + D * a 1) * B := by ring
        _ = 0 := by rw [hR1, hR2]; ring
    have hBMul : a 1 * (A * D - B * C) = 0 := by
      calc
        a 1 * (A * D - B * C) =
            A * (C * a 0 + D * a 1) -
              C * (A * a 0 + B * a 1) := by ring
        _ = 0 := by rw [hR1, hR2]; ring
    have ha0 : a 0 = 0 := (mul_eq_zero.mp hAMul).resolve_right hDet
    have ha1 : a 1 = 0 := (mul_eq_zero.mp hBMul).resolve_right hDet
    apply ha
    funext i
    fin_cases i
    · exact ha0
    · exact ha1
  have hPos (a : Fin 2 → ℝ) (ha : a ≠ 0) : 0 < q a := by
    rcases hDetected a ha with hx | hy
    · have hxSq : 0 < (A * a 0 + B * a 1) ^ 2 :=
        sq_pos_of_ne_zero hx
      dsimp [q]
      nlinarith [sq_nonneg (C * a 0 + D * a 1)]
    · have hySq : 0 < (C * a 0 + D * a 1) ^ 2 :=
        sq_pos_of_ne_zero hy
      dsimp [q]
      nlinarith [sq_nonneg (A * a 0 + B * a 1)]
  obtain ⟨m, M, hm, hM, hBounds⟩ :=
    p4Q2HR_continuous_pos_quadratic_norm_bounds q hCont hHom hPos
  refine ⟨z, z', m, hm, ?_⟩
  intro a
  have hEq :
      p4Q2PZ37ZL_originalStaticTwoModeGISOS H b hb.le e e' z z' a = q a := by
    change
      (a 0 * A + a 1 * B) ^ 2 + (a 0 * C + a 1 * D) ^ 2 =
        (A * a 0 + B * a 1) ^ 2 + (C * a 0 + D * a 1) ^ 2
    ring
  rw [hEq]
  exact (hBounds a).1

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZL_originalStaticTwoModeGISOS_exists_positive_floor
