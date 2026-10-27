import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLPositiveFineFrameObstructionV5_PZ37ZF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorPhysicalCoercivityV5_PZ37U
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZG — actual Wilson full-link GL / nonzero physical-source Rayleigh ratio

Fix the unmodified SU(2) Wilson normalized physical transfer, its canonical
Gauss-law Hilbert source, the genuine TWO INTERACTING Wilson posteriors, and
the original FULL spatial-link / FULL boundary-pair Haar GL mass.

At any finite H and positive frozen b, for every nonzero physical source f,

  0 <= M_GL(H,b;f) / ||f||^2 <= 2 |Links(H)| / exp(-16*b).

In particular this upper estimate applies at every sufficiently small,
strictly positive fine t to the actual nonzero cancellation source
F_t=U-T_t U, with NO small-fine factor multiplying its normalized ratio.

The original all-depth PZ37U kernel-comparison theorem additionally gives
a strictly positive MODEL-DEPENDENT Rayleigh floor on each finite original
Krylov source subspace (restricted to nonzero physical sources). It may
depend on fine t, depth, volume, and the actual Wilson context.

Neither the vanishing mass M_GL(F_t)->0 nor the two-mode coefficient-frame
no-go proves R(F_t)->0, or refutes Hilbert-source coercivity. We do not
claim a fine-uniform lower floor, an H-uniform lower floor, endpoint E,
arbitrary-depth common fine interval F, H1-H4 or continuum mass gap.
No surrogate posterior, Dobrushin, new axiom, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZG_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact original Wilson full-link Rayleigh numerator per unit
physical Gauss-law Hilbert squared norm. Only f != 0 is interpreted
as an actual normalized Rayleigh quotient; no endpoint 0/0 claim. -/
noncomputable def p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) : ℝ :=
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb) f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) / ‖f‖ ^ 2

/-- Explicit genuinely interacting Wilson source-norm upper factor,
not a positive coercivity constant. -/
noncomputable def p4Q2PZ37ZG_originalFullLinkGL_RayleighCap
    (H : ℕ) (b : ℝ) : ℝ :=
  ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
    Real.exp (-16 * b)

/-- The actual variance-normalized two-original-posterior expectation-gap
Haar square is nonnegative, including its ALL-link spatial sum. -/
theorem p4Q2PZ37ZG_originalGL_fullLink_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    0 ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb) f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  apply Finset.sum_nonneg
  intro e _he
  unfold p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  apply integral_nonneg
  intro z
  exact div_nonneg (sq_nonneg _)
    (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H b hb z.2 e).le

/-- TRUE original Wilson full-link posterior Rayleigh for EVERY nonzero
physical Haar-L2 source is bounded above by the explicit link-count
factor at fixed H,b. No fine-coupling or source-depth restriction. -/
theorem p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hf : f ≠ 0) :
    0 ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb f ∧
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb f ≤
        p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
  have hNorm : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) 2
  have hMass :
      0 ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    p4Q2PZ37ZG_originalGL_fullLink_nonneg H b hb f
  have hWilson :=
    p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm H b hb f
  constructor
  · unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
    exact div_nonneg hMass hNorm.le
  · unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
    apply (div_le_iff₀ hNorm).2
    calc
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb) f
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (2 * ‖f‖ ^ 2)) / Real.exp (-16 * b) := hWilson
      _ = p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b * ‖f‖ ^ 2 := by
        unfold p4Q2PZ37ZG_originalFullLinkGL_RayleighCap
        ring

/-- At each fixed finite Wilson model, PZ37U genuinely controls the
source-normalized GL Rayleigh from BELOW on ALL finite-depth actual
Krylov physical sources, as long as the physical source is nonzero.
The lower constant is allowed to depend on the true fine and contexts.
The UPPER cap is independent of fine and depth at fixed H,b. -/
theorem p4Q2PZ37ZG_allFinite_allDepth_nonzeroOriginalSource_Rayleigh_bounds
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (hFrozen : 0 < beta n)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
      (halfExtent (n + 1)) 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ a : Fin (r + 1) → ℝ,
        p4Q2HJ_actualRightPhysicalSourceSynthesis
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a ≠ 0 →
        c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
          (halfExtent (n + 1)) (beta n) hFrozen
          (p4Q2HJ_actualRightPhysicalSourceSynthesis
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) ∧
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
          (halfExtent (n + 1)) (beta n) hFrozen
          (p4Q2HJ_actualRightPhysicalSourceSynthesis
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) ≤
          p4Q2PZ37ZG_originalFullLinkGL_RayleighCap
            (halfExtent (n + 1)) (beta n) := by
  let S :=
    p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  obtain ⟨c, _C, hc, _hcC, hCompare⟩ :=
    p4Q2PZ37U_allFinite_allDepth_originalPosteriorMass_physicalNorm_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen e left₀
  refine ⟨c, hc, ?_⟩
  intro a ha
  let f := S a
  have hf : f ≠ 0 := ha
  have hNorm : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) 2
  have hLower :
      c * ‖f‖ ^ 2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          (halfExtent (n + 1)) (beta n) (le_of_lt hFrozen) f
          (Finset.univ : Finset
            (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))) :=
    (hCompare a).1
  have hLowerRatio :
      c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        (halfExtent (n + 1)) (beta n) hFrozen f := by
    unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
    exact (le_div_iff₀ hNorm).2 hLower
  have hUpperRatio :=
    (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
      (halfExtent (n + 1)) (beta n) hFrozen f hf).2
  exact ⟨hLowerRatio, hUpperRatio⟩

/-- The original unit U minus its real fine Wilson transfer T_t U
has a bounded physical-normalized GL Rayleigh on a genuine STRICT
positive-fine interval. Its source is nonzero there (PZ37ZF).
Unlike the unnormalized GL mass, this bound has no factor tending
to zero as t approaches zero. -/
theorem p4Q2PZ37ZG_positiveFine_originalPhysicalCancellation_Rayleigh_bounds
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
        p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0 ∧
        0 ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) ∧
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) ≤
          p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
  obtain ⟨delta, hDelta, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  refine ⟨delta, hDelta, ?_⟩
  intro t ht hSmall
  have hf := hNonzero t ht hSmall
  exact ⟨hf,
    (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t) hf).1,
    (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t) hf).2⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZG_originalGL_fullLink_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZG_allFinite_allDepth_nonzeroOriginalSource_Rayleigh_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZG_positiveFine_originalPhysicalCancellation_Rayleigh_bounds
