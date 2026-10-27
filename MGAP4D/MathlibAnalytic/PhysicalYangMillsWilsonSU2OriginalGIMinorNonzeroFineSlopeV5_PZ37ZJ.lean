import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLQuadraticFineBudgetV5_PZ37ZI
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZJ — genuine original two-Wilson-posterior GI transverse fine slope

The actual JG strong Haar-L² derivative and JI original two-posterior
GI derivative identify the first-order raw Wilson right-Haar-row minor
with -1/2 times the spatial-Wilson/static-unit original GI minor.
Crucially, LM proved the latter determinant is NONZERO at actual
complete spatial SU(2) pair-boundary contexts for any finite H,
positive frozen coupling, and given genuine links.

Here we strengthen JI's "nonzero at positive fine" to the genuine
quantitative FIRST-ORDER positive-fine lower bound

    c_(H,b,contexts) t ≤ |M_raw(t)|,    0<t<delta,

where M_raw(t) is the signed determinant of the ORIGINAL two interacting
Wilson posterior GI responses to the true Haar constant and genuine
unnormalized one-slab Wilson Haar row. No artificial test vector or
independent-Haar posterior is substituted.

The determinant annihilates every scalar multiple of the physical
constant source, making its first variation a normalization-insensitive
transverse observable. A lower bound for the original norm-normalized
physical F_t (or its Rayleigh quotient) needs a separate quantitative
bounded receiver/norm-normalizer transfer, not silently assumed here.

No Dobrushin, new axiom, sorry, admit, native_decide, Gray substitution,
volume-uniform gap, endpoint E, all-depth F, H1-H4 or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The exact nonzero first derivative of the ORIGINAL raw Wilson
two-context GI minor, by JI, is the genuine static spatial-action
minor multiplied by -1/2. -/
theorem p4Q2PZ37ZJ_originalRawGIMinor_slope_tendsto
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Tendsto
      (fun t : ℝ => t⁻¹ *
        p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(1 / 2 : ℝ) *
        p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z')) := by
  have hDeriv :=
    (p4Q2JI_originalGIRawFineRowMinor_hasDerivAt_zero
      H b hb.le e e' z z').tendsto_slope_zero_right
  have hZero :=
    p4Q2JI_originalGIRawFineRowMinor_zero H b hb.le e e' z z'
  simpa only [zero_add, hZero, sub_zero, smul_eq_mul] using hDeriv

/-- Original LM gives a genuine SU(2) pair of contexts where the
signed two-posterior raw minor has a STRICTLY NONZERO first-order fine
slope. This does not assume physical transfer normalization derivatives. -/
theorem p4Q2PZ37ZJ_originalRawGIMinor_exists_nonzero_slope
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (-(1 / 2 : ℝ) *
        p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z') ≠ 0 ∧
      Tendsto
        (fun t : ℝ => t⁻¹ *
          p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(1 / 2 : ℝ) *
          p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z')) := by
  obtain ⟨z, z', hW⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  exact ⟨z, z', mul_ne_zero (by norm_num) hW,
    p4Q2PZ37ZJ_originalRawGIMinor_slope_tendsto H b hb e e' z z'⟩

/-- A NONZERO original Wilson GI minor derivative yields a positive
literal lower coefficient for |minor(t)|/t on an entire punctured
positive-fine interval. The coefficient depends on the actual model
and contexts. This conclusion is strictly stronger than mere
nonvanishing of the minor. -/
theorem p4Q2PZ37ZJ_originalRawGIMinor_linearLower_of_spatialMinor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hW : p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' ≠ 0) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
      ∀ t : ℝ, 0 < t → t < delta →
        c * t ≤ |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| := by
  let D : ℝ :=
    -(1 / 2 : ℝ) *
      p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z'
  have hD : 0 < |D| := abs_pos.mpr (mul_ne_zero (by norm_num) hW)
  let c : ℝ := |D| / 2
  have hc : 0 < c := half_pos hD
  have hSlope :=
    p4Q2PZ37ZJ_originalRawGIMinor_slope_tendsto H b hb e e' z z'
  have hAbs :
      Tendsto
        (fun t : ℝ =>
          |t⁻¹ * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t|)
        (𝓝[>] (0 : ℝ)) (𝓝 |D|) :=
    (continuous_abs.tendsto D).comp hSlope
  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        c < |t⁻¹ * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| :=
    hAbs.eventually (isOpen_Ioi.mem_nhds (by dsimp [c]; linarith))
  have hNhds :
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        0 < t →
          c < |t⁻¹ * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| :=
    (eventually_nhdsWithin_iff).mp hEventually
  obtain ⟨delta, hDelta, hBall⟩ :=
    (Metric.eventually_nhds_iff).mp hNhds
  refine ⟨delta, c, hDelta, hc, ?_⟩
  intro t ht hSmall
  have hNear : dist t (0 : ℝ) < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using hSmall
  have hLower :
      c ≤ |t⁻¹ * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| :=
    le_of_lt (hBall hNear ht)
  calc
    c * t ≤
        |t⁻¹ * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| * t :=
      mul_le_mul_of_nonneg_right hLower ht.le
    _ = |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| := by
      rw [abs_mul, abs_inv, abs_of_pos ht]
      calc
        (t⁻¹ * |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t|) * t =
            (t⁻¹ * t) *
              |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| := by ring
        _ = _ := by rw [inv_mul_cancel₀ ht.ne', one_mul]

/-- UNCONDITIONAL ORIGINAL Wilson link/context witnesses give a
quantitative positive-fine first-order lower bound for the
two-posterior GI raw minor. No finite-volume-uniform coefficient
or new positive source-norm lower bound is inserted. -/
theorem p4Q2PZ37ZJ_originalRawGIMinor_exists_linearLower
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
        ∀ t : ℝ, 0 < t → t < delta →
          c * t ≤ |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' t| := by
  obtain ⟨z, z', hW⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  obtain ⟨delta, c, hDelta, hc, hLower⟩ :=
    p4Q2PZ37ZJ_originalRawGIMinor_linearLower_of_spatialMinor
      H b hb e e' z z' hW
  exact ⟨z, z', delta, c, hDelta, hc, hLower⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZJ_originalRawGIMinor_slope_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZJ_originalRawGIMinor_exists_nonzero_slope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZJ_originalRawGIMinor_linearLower_of_spatialMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZJ_originalRawGIMinor_exists_linearLower
