import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualWilsonDepthOneAnchorPivotV5_IS
import Mathlib.Tactic

/-!
# P4-Q2-IT: exact authentic Wilson two-context minors vs physical Haar-L² source Gram

IS constructs the NONZERO anchored depth-one coefficient pivot
  w = d0 v1 - d1 v0
at an actual (link, full SU(2) pair-boundary) original Wilson GI context
with d0 != 0, for positive frozen beta(n) and arbitrary fine beta(n+1)>=0.

IT closes the exact finite-model *diagnostic*, not the missing analytic
nonvanishing theorem, by combining:
  * every other ORIGINAL interacting-Wilson two-posterior response
    on w is literally its two-context 2x2 determinant;
  * the TRUE physical Haar-L² source Gram quadratic at w equals
    the squared norm of the actual physical synthesis S(w);
  * the original GL mass of S(w) is zero precisely when ALL genuine
    Wilson two-context determinants vanish;
  * the actual physically invisible Hilbert sector is NONZERO precisely
    when the pivot has strictly POSITIVE physical Gram but ALL original
    Wilson two-context minors vanish;
  * a global original Wilson GL/source norm lower bound exists precisely
    when the pivot source Gram vanishes OR at least one second genuine
    Wilson context yields a NONZERO two-row determinant.

The two mutually exclusive diagnostics distinguish a merely dependent
Krylov coefficient from a genuinely nonzero GI-invisible PHYSICAL source.
No assumption or proof that the determinant is nonzero in the positive
fine-coupling depth-one model; no independent-Haar posterior, invented
source frame, Dobrushin, volume/scale-uniform coercivity, H1-C3, OS
Hamiltonian, or continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IT_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The determinant of TWO actual scalar GI modal detection rows on
the literal zero/first-depth coefficient selectors. -/
noncomputable def p4Q2IT_depthOneTwoContextMinor
    (D D' : (Fin (1 + 1) → ℝ) →ₗ[ℝ] ℝ) : ℝ :=
  D (p4Q2GX_rightZeroCoefficient 1) * D' p4Q2IS_depthOneCoefficient -
    D p4Q2IS_depthOneCoefficient *
      D' (p4Q2GX_rightZeroCoefficient 1)

/-- Second original two-Wilson-posterior context response of the
anchored pivot IS the genuine 2x2 GI minor. -/
theorem p4Q2IT_depthOneTwoContextMinor_eq_pivotResponse
    (D D' : (Fin (1 + 1) → ℝ) →ₗ[ℝ] ℝ) :
    p4Q2IT_depthOneTwoContextMinor D D' =
      D' (p4Q2IS_depthOnePivot D) := by
  exact (p4Q2IS_depthOnePivot_secondDetector_determinant D D').symm

section ActualRightDepthOne

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (1 + 1) → ℝ
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "FullDetector" =>
  p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- Explicit genuine Haar-L² source Gram evaluation on the actual
depth-one Wilson pivot; no independence of the fine Krylov modes. -/
theorem p4Q2IT_actualDepthOne_pivot_physicalGram_eq_sourceNormSq
    (D : Coeff →ₗ[ℝ] ℝ) :
    star (p4Q2IS_depthOnePivot D) ⬝ᵥ
      (Qsrc *ᵥ (p4Q2IS_depthOnePivot D)) =
      ‖PhysicalSource (p4Q2IS_depthOnePivot D)‖ ^ 2 := by
  exact p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n 1 (p4Q2IS_depthOnePivot D)

/-- The physical source Gram at the pivot vanishes exactly when its
LITERAL gauge-invariant Haar-L² synthesized physical source vanishes. -/
theorem p4Q2IT_actualDepthOne_pivot_physicalGram_zero_iff_source_zero
    (D : Coeff →ₗ[ℝ] ℝ) :
    (star (p4Q2IS_depthOnePivot D) ⬝ᵥ
      (Qsrc *ᵥ (p4Q2IS_depthOnePivot D)) = 0) ↔
      PhysicalSource (p4Q2IS_depthOnePivot D) = 0 := by
  rw [p4Q2IT_actualDepthOne_pivot_physicalGram_eq_sourceNormSq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n D]
  constructor
  · intro h
    have hNorm : ‖PhysicalSource (p4Q2IS_depthOnePivot D)‖ = 0 := by
      nlinarith
    exact norm_eq_zero.mp hNorm
  · intro h
    rw [h]
    norm_num

/-- The genuine Haar-L² quadratic Gram on the anchored pivot is
strictly positive exactly when its synthesized physical source is
NONZERO, rather than merely a nonzero formal coefficient vector. -/
theorem p4Q2IT_actualDepthOne_pivot_physicalGram_pos_iff_source_nonzero
    (D : Coeff →ₗ[ℝ] ℝ) :
    (0 < star (p4Q2IS_depthOnePivot D) ⬝ᵥ
      (Qsrc *ᵥ (p4Q2IS_depthOnePivot D))) ↔
      PhysicalSource (p4Q2IS_depthOnePivot D) ≠ 0 := by
  rw [p4Q2IT_actualDepthOne_pivot_physicalGram_eq_sourceNormSq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n D]
  constructor
  · intro h hzero
    rw [hzero] at h
    norm_num at h
  · intro h
    exact pow_pos (norm_pos_iff.mpr h) 2

/-- Vanishing of the ORIGINAL complete two-interacting-Wilson GI
detector of the anchored depth-one pivot is exactly simultaneous
vanishing of all literal two-context Wilson 2x2 response minors. -/
theorem p4Q2IT_actualDepthOne_allOriginalWilsonMinors_zero_iff_pivotGI_zero
    (e : Link) (z : Pair) :
    (∀ e' : Link, ∀ z' : Pair,
      p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') = 0) ↔
      FullDetector (p4Q2IS_depthOnePivot (Modal e z)) = 0 := by
  constructor
  · intro h
    funext e'
    apply ContinuousMap.ext
    intro z'
    change Modal e' z' (p4Q2IS_depthOnePivot (Modal e z)) = 0
    rw [← p4Q2IT_depthOneTwoContextMinor_eq_pivotResponse]
    exact h e' z'
  · intro h e' z'
    have hEval := congrArg
      (fun F : Link → C(Pair, ℝ) => F e' z') h
    have hZero :
        Modal e' z' (p4Q2IS_depthOnePivot (Modal e z)) = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hEval
    exact (p4Q2IT_depthOneTwoContextMinor_eq_pivotResponse
      (Modal e z) (Modal e' z')).trans hZero

/-- The ORIGINAL Wilson physical GL integral mass of the actual
depth-one pivot vanishes precisely when EVERY genuine original
two-posterior GI minor against the anchored Wilson context vanishes.
No replacement conditional Haar posterior is used. -/
theorem p4Q2IT_actualDepthOne_originalGLMass_zero_iff_allWilsonMinors_zero
    (hFrozen : 0 < beta n) (e : Link) (z : Pair) :
    OriginalMass (PhysicalSource (p4Q2IS_depthOnePivot (Modal e z)))
      (Finset.univ : Finset Link) = 0 ↔
      ∀ e' : Link, ∀ z' : Pair,
        p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') = 0 := by
  have hMass :=
    p4Q2HJ_actualRightGLMass_zero_iff_continuousDetector_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 hFrozen (p4Q2IS_depthOnePivot (Modal e z))
  exact hMass.trans
    (p4Q2IT_actualDepthOne_allOriginalWilsonMinors_zero_iff_pivotGI_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z).symm

/-- Complete fixed-model YES/NO witness for actual physical
invisibility at depth one: a genuine nonzero physically GI-invisible
source exists IFF the anchored physical Gram is strictly positive AND
all original interacting-Wilson GI two-context minors vanish.

The witness context is supplied by HY for ANY fine beta>=0.
The theorem does not assert which side occurs for positive fine beta. -/
theorem p4Q2IT_actualDepthOne_invisibleSector_iff_positivePhysicalGram_and_allWilsonMinors_zero
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ z : Pair,
      Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
      (Invisible ≠ ⊥ ↔
        (0 < star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
          (Qsrc *ᵥ (p4Q2IS_depthOnePivot (Modal e z)))) ∧
        (∀ e' : Link, ∀ z' : Pair,
          p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') = 0)) := by
  obtain ⟨z, hAnchor, _hPivotNonzero, _hPivotAtAnchor, hCriterion⟩ :=
    p4Q2IS_actualRightDepthOne_originalWilsonAnchorPivot_criterion
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_⟩
  have hSep :
      Invisible = ⊥ ↔ (PhysicalSource).ker = (FullDetector).ker := by
    rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel]
    exact p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  have hObstruction := not_congr (hSep.trans hCriterion)
  have hObstruction' :
      Invisible ≠ ⊥ ↔
        PhysicalSource (p4Q2IS_depthOnePivot (Modal e z)) ≠ 0 ∧
        FullDetector (p4Q2IS_depthOnePivot (Modal e z)) = 0 := by
    simpa only [not_or, not_not] using hObstruction
  exact hObstruction'.trans
    (and_congr
      (p4Q2IT_actualDepthOne_pivot_physicalGram_pos_iff_source_nonzero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (Modal e z)).symm
      (p4Q2IT_actualDepthOne_allOriginalWilsonMinors_zero_iff_pivotGI_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z).symm)

/-- Explicit authentic-Wilson finite-model GLOBAL lower-bound
criterion: a strictly positive original GL-mass/source Haar-L² lower
floor on ALL actual physical sources exists iff the depth-one
anchored pivot has zero physical Gram OR some second ACTUAL Wilson
link/pair-boundary context yields a nonzero 2x2 GI determinant.

This is an equivalence, not an unconditional lower bound. -/
theorem p4Q2IT_actualDepthOne_globalOriginalGLFloor_iff_zeroPhysicalPivot_or_nonzeroWilsonMinor
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ z : Pair,
      Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
      ((∃ c : ℝ, 0 < c ∧
        ∀ f : ↥((PhysicalSource).range),
          c * ‖(f : Phys)‖ ^ 2 ≤
            OriginalMass (f : Phys) (Finset.univ : Finset Link)) ↔
        (star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
          (Qsrc *ᵥ (p4Q2IS_depthOnePivot (Modal e z))) = 0) ∨
        (∃ e' : Link, ∃ z' : Pair,
          p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') ≠ 0)) := by
  obtain ⟨z, hAnchor, _hPivotNonzero, _hPivotAtAnchor, hCriterion⟩ :=
    p4Q2IS_actualRightDepthOne_originalWilsonAnchorPivot_criterion
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_⟩
  have hSep :
      Invisible = ⊥ ↔ (PhysicalSource).ker = (FullDetector).ker := by
    rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel]
    exact p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
  have hAll :=
    p4Q2IT_actualDepthOne_allOriginalWilsonMinors_zero_iff_pivotGI_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z
  have hExists :
      FullDetector (p4Q2IS_depthOnePivot (Modal e z)) ≠ 0 ↔
      (∃ e' : Link, ∃ z' : Pair,
        p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') ≠ 0) := by
    constructor
    · intro hNonzero
      by_contra hNone
      apply hNonzero
      apply hAll.mp
      intro e' z'
      by_contra hDet
      exact hNone ⟨e', z', hDet⟩
    · rintro ⟨e', z', hDet⟩ hZero
      exact hDet ((hAll.mpr hZero) e' z')
  calc
    (∃ c : ℝ, 0 < c ∧
      ∀ f : ↥((PhysicalSource).range),
        c * ‖(f : Phys)‖ ^ 2 ≤
          OriginalMass (f : Phys) (Finset.univ : Finset Link)) ↔
        Invisible = ⊥ :=
      (p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_lower
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 1 hFrozen).symm
    _ ↔ (PhysicalSource).ker = (FullDetector).ker := hSep
    _ ↔ PhysicalSource (p4Q2IS_depthOnePivot (Modal e z)) = 0 ∨
          FullDetector (p4Q2IS_depthOnePivot (Modal e z)) ≠ 0 := hCriterion
    _ ↔ (star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
           (Qsrc *ᵥ (p4Q2IS_depthOnePivot (Modal e z))) = 0) ∨
          (∃ e' : Link, ∃ z' : Pair,
            p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') ≠ 0) :=
      or_congr
        (p4Q2IT_actualDepthOne_pivot_physicalGram_zero_iff_source_zero
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (Modal e z)).symm
        hExists

end ActualRightDepthOne
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_depthOneTwoContextMinor_eq_pivotResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_pivot_physicalGram_eq_sourceNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_pivot_physicalGram_zero_iff_source_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_pivot_physicalGram_pos_iff_source_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_allOriginalWilsonMinors_zero_iff_pivotGI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_originalGLMass_zero_iff_allWilsonMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_invisibleSector_iff_positivePhysicalGram_and_allWilsonMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IT_actualDepthOne_globalOriginalGLFloor_iff_zeroPhysicalPivot_or_nonzeroWilsonMinor
