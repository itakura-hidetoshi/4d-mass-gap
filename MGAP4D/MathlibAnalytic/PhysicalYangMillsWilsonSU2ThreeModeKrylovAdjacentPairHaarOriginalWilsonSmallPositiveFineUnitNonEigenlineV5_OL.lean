import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonCrossingMeanInvariantV5_IX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineEigenlineAllDepthCrossMinorObstructionV5_OK
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# P4-Q2-OL — genuine small-positive-fine SU(2) Wilson unit is NOT an eigenline

This is a genuinely new positive-fine physical noncollinearity witness,
not a conditional detector-frame assumption.

IX already proved that at beta=0 the derivative of the difference of
two original one-slab *Haar reference* integral rows equals -1/2
times their difference of original spatial Wilson plaquette actions.
IY explicitly constructs TWO actual even-periodic SU(2) spatial
boundaries: all identity with W=0 and a central-twist boundary W>=2.

Consequently the derivative of the real original Wilson Haar row
difference at zero is strictly positive (at least 1). Since both
rows equal one at zero, a genuine strictly positive fine-coupling
interval exists where the original Haar-row values differ.

IV proves the EXACT bridge from pointwise genuine one-slab Haar-row
nonconstancy to the true normalized FINE Wilson Gauss-law physical
operator T_t on U: the first real fine right-Krylov physical source
T_t U is NOT in the one-dimensional physical unit line.

At every finite H, an interval (0, delta_H) of ORIGINAL positive fine
couplings has this property, irrespective of the independent frozen
coupling. With frozen beta(n)>0, the actual HY/IS original two-Wilson-
posterior GI anchor selects a nonzero true physical depth-one pivot
which is GI-null at exactly its selected original context. This
does not prove that another actual GI context detects the pivot.

The original two interacting Wilson posterior laws, FF receiver, full
Gauss-law physical Hilbert carrier, true spatial/temporal Wilson action,
Perron half-density, and fine/frozen coupling distinction remain intact.
No extra source-rank hypothesis, Haar-posterior substitution, sorry,
admit or unproved axiom. Actual nonzero GI cross-context minor,
all-depth positive-fine physical-source separation, U0, endpoint,
strong limit and continuum 4D Yang--Mills mass gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Standard mathlib slope argument: a differentiable real function
with f(0)=0 and strictly positive derivative at zero is strictly
positive on a real interval immediately to the RIGHT of zero. -/
private theorem p4Q2OL_abstract_derivative_positive_right
    (f : ℝ → ℝ) (d : ℝ)
    (hf : HasDerivAt f d 0) (hd : 0 < d) (hzero : f 0 = 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 < t → t < delta → 0 < f t := by
  have hTendsto := hf.tendsto_slope_zero_right
  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        0 < t⁻¹ • (f (0 + t) - f 0) :=
    hTendsto.eventually (eventually_gt_nhds hd)
  have hNear :
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        t ∈ Set.Ioi (0 : ℝ) →
          0 < t⁻¹ • (f (0 + t) - f 0) :=
    (eventually_nhdsWithin_iff).mp hEventually
  obtain ⟨delta, hdelta, hBound⟩ :=
    (Metric.eventually_nhds_iff).mp hNear
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hlt
  have hDist : dist t 0 < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using hlt
  have hSlope : 0 < t⁻¹ * f t := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using
      (hBound hDist ht)
  have hProduct : 0 < t * (t⁻¹ * f t) := mul_pos ht hSlope
  simpa only [mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), one_mul] using hProduct

section GenuineOriginalSmallBeta
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Row" =>
  p4Q2IV_originalWilsonUnitHaarKernelSection H

private def p4Q2OL_identityBoundary : Cfg := fun _ => 1
private noncomputable def p4Q2OL_twistedBoundary : Cfg :=
  periodicHypercubicEvenSpatialSliceRestriction
    (p4Q2IY_onePrimaryLinkCentralTwist H)

/-- The beta-zero derivative of the difference of TWO literal
original SU(2) Wilson one-slab Haar rows is at least ONE.
This positive derivative is proved using the IY nonconstant physical
spatial plaquette action and IX crossing-action Haar invariance. -/
theorem p4Q2OL_originalTwoPhysicalHaarRows_derivative_pos :
    ∃ d : ℝ, 0 < d ∧
      HasDerivAt
        (fun t : ℝ =>
          Row t (p4Q2OL_identityBoundary H) -
            Row t (p4Q2OL_twistedBoundary H))
        d 0 := by
  let B₀ : Cfg := p4Q2OL_identityBoundary H
  let B₁ : Cfg := p4Q2OL_twistedBoundary H
  let d : ℝ := -(1 / 2 : ℝ) * (W B₀ - W B₁)
  have hZero : W B₀ = 0 :=
    p4Q2IY_allOneSpatialWilsonAction_zero H
  have hTwist : (2 : ℝ) ≤ W B₁ :=
    p4Q2IY_actualSpatialWilsonAction_twist_ge_two H
  have hPositive : 0 < d := by
    dsimp [d]
    rw [hZero]
    linarith
  refine ⟨d, hPositive, ?_⟩
  exact p4Q2IX_originalWilsonTwoRowDifference_hasDerivAt_zero H B₀ B₁

/-- Main original analytic witness: at EACH finite SU(2) even-periodic
spatial lattice H the same TWO explicit physical boundaries (identity
and twisted primary Wilson plaquette) have strictly ordered true
one-slab Haar rows for EVERY sufficiently small POSITIVE coupling. -/
theorem p4Q2OL_originalWilsonHaarRows_strict_smallPositive :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 < t → t < delta →
        Row t (p4Q2OL_twistedBoundary H) <
          Row t (p4Q2OL_identityBoundary H) := by
  let f : ℝ → ℝ :=
    fun t => Row t (p4Q2OL_identityBoundary H) -
      Row t (p4Q2OL_twistedBoundary H)
  obtain ⟨d, hd, hDeriv⟩ :=
    p4Q2OL_originalTwoPhysicalHaarRows_derivative_pos H
  have hAtZero : f 0 = 0 := by
    dsimp [f]
    rw [p4Q2IW_originalWilsonHaarRow_beta_zero,
      p4Q2IW_originalWilsonHaarRow_beta_zero]
    norm_num
  obtain ⟨delta, hdelta, hpos⟩ :=
    p4Q2OL_abstract_derivative_positive_right f d hDeriv hd hAtZero
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hlt
  have h := hpos t ht hlt
  dsimp [f] at h
  linarith

/-- The genuine original one-slab Haar row is NOT constant at every
small positive fine coupling at any finite spatial Wilson volume.
The witness involves actual physical SU(2) boundary configurations. -/
theorem p4Q2OL_originalWilsonHaarRows_notConstant_smallPositive :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 < t → t < delta →
        ∃ B₀ B₁ : Cfg, Row t B₀ ≠ Row t B₁ := by
  obtain ⟨delta, hdelta, hsep⟩ :=
    p4Q2OL_originalWilsonHaarRows_strict_smallPositive H
  exact ⟨delta, hdelta, fun t ht hlt =>
    ⟨p4Q2OL_identityBoundary H, p4Q2OL_twistedBoundary H,
      ne_of_gt (hsep t ht hlt) |>.symm⟩⟩

end GenuineOriginalSmallBeta

section ActualFinePhysical
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- UNCONDITIONAL positive-fine physical non-eigenline in an explicitly
delimited (volume-dependent) interval: the actual normalized fine
Wilson transfer of the physical constant source U is not collinear
with U. No detector-rank or nonzero GI minor assumption is used. -/
theorem p4Q2OL_actualFineWilsonUnit_notEigenline_smallPositive :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ¬ ∃ c : ℝ, Fine Unit = c • Unit) := by
  obtain ⟨delta, hdelta, hsep⟩ :=
    p4Q2OL_originalWilsonHaarRows_notConstant_smallPositive Hn
  refine ⟨delta, hdelta, ?_⟩
  intro ht hlt
  apply (p4Q2IV_actualFineUnit_notEigenline_iff_two_rawWilson_boundaries
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n).mpr
  exact hsep (beta (n + 1)) ht hlt

/-- At small genuine positive fine coupling with positive frozen
Wilson beta, an ACTUAL original-HY/IS selected zero-depth signed
two-posterior GI row annihilates a NONZERO genuine Gauss-law physical
source obtained from the true FIRST fine right Krylov mode.

Only the single original selected row is proved to annihilate this
source. This is NOT a globally GI-invisible physical source, and does
NOT produce a nonzero OJ two-context minor. -/
theorem p4Q2OL_actualDepthOne_nonzeroPhysical_oneRowGI_null_smallFine
    (hFrozen : 0 < beta n)
    (right : Cfg) (e : Link) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∃ z : Pair,
          M 1 e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
          S 1 (p4Q2IS_depthOnePivot (M 1 e z)) ≠ 0 ∧
          M 1 e z (p4Q2IS_depthOnePivot (M 1 e z)) = 0) := by
  obtain ⟨delta, hdelta, hNotEigen⟩ :=
    p4Q2OL_actualFineWilsonUnit_notEigenline_smallPositive
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  refine ⟨delta, hdelta, ?_⟩
  intro ht hlt
  obtain ⟨z, hAnchor, _hPivotNe, hPivotZero, _hCriterion⟩ :=
    p4Q2IS_actualRightDepthOne_originalWilsonAnchorPivot_criterion
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_, hPivotZero⟩
  intro hSource
  apply hNotEigen ht hlt
  exact (p4Q2IU_actualDepthOne_pivotPhysicalZero_iff_fineUnitEigenline
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e z hAnchor).mp hSource

end ActualFinePhysical
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OL_originalTwoPhysicalHaarRows_derivative_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OL_originalWilsonHaarRows_strict_smallPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OL_originalWilsonHaarRows_notConstant_smallPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OL_actualFineWilsonUnit_notEigenline_smallPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OL_actualDepthOne_nonzeroPhysical_oneRowGI_null_smallFine
