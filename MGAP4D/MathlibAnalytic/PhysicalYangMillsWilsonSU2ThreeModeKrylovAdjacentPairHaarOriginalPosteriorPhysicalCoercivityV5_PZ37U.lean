import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramQuantitativeQuadraticV5_PZ37T
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLPhysicalSourceGlobalCoercivityCriterionV5_IJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllFineUnconditionalGLMassV5_OX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37U — the genuine posterior/source quantitative bridge

The SAME original SU(2) Wilson two-interacting-posterior mass has two
independently established, exact zero loci for all finite Krylov depths:
* OX: original full-link GL mass is zero iff the authentic Gauss-law
  physical Hilbert synthesis is zero (positive frozen coupling).
* HI: original full-link GL mass is zero iff the coefficient belongs
  to the original all-boundary two-posterior GI joint kernel.

Therefore their coefficient kernels are EQUAL, without a source
separation axiom. IJ's previously conditional physical-source norm
comparison becomes unconditional at every finite volume, all finite
right-Krylov depths, and all nonnegative fine couplings.

For the first three modes, combine the physical norm comparison with
PZ37T's exact spectral Gram bound B(H,t) = 4D3/(m0+m2+m4)^2.
The genuine posterior-fiber mass obeys

  c(H,b,t) * B(H,t) * (a0^2+a1^2+a2^2)
       <= original GL mass(S_2(a))
       <= C(H,b,t) * ‖S_2(a)‖^2

at every finite spatial H >= 0 and sufficiently small positive fine t.

The strictly positive c, C and small-fine radius may depend on H,
couplings, depth or genuine physical contexts. This does NOT prove a
volume-independent posterior mass floor U0, positive fine at arbitrary
depth with a common radius, endpoint source transport, the continuum
strong limit or a Yang--Mills mass gap. No model substitution, new
axiom, sorry, admit, or native_decide.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37U_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37U_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37U_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37U_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37U_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37U_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section AllDepthTruePhysicalPosterior
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "S" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "K" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The two independently proved original Wilson posterior zero-locus
theorems identify the exact all-context GI kernel with the genuine
physical Hilbert source kernel at every finite depth and fine t >= 0.
This is NOT an assertion of coefficient independence. -/
theorem p4Q2PZ37U_allFinite_allDepth_originalSourceKernel_eq_GIJoint
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    (p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).ker = K := by
  ext a
  have hPhysical :=
    p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ r a
  have hGI :=
    p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a
  change (S a = 0) ↔ a ∈ K
  exact hPhysical.symm.trans hGI

/-- Model-dependent, strictly positive, two-sided comparison between
the UNMODIFIED original two-interacting-Wilson-posterior Haar mass
and the genuine Gauss-law physical Hilbert source norm. This holds
at all finite Krylov depths, at every nonnegative fine coupling.
The constants are not volume-, fine-, or depth-uniform. -/
theorem p4Q2PZ37U_allFinite_allDepth_originalPosteriorMass_physicalNorm_compare
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * ‖S a‖ ^ 2 ≤ Mass (S a) (Finset.univ : Finset Link) ∧
        Mass (S a) (Finset.univ : Finset Link) ≤ C * ‖S a‖ ^ 2 := by
  exact p4Q2IJ_originalWilson_sourceSeparation_implies_global_GL_sourceNorm
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen
    (p4Q2PZ37U_allFinite_allDepth_originalSourceKernel_eq_GIJoint
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen e left₀)

end AllDepthTruePhysicalPosterior

section ThreeModeQuantitativePosterior
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "Krylov" =>
  (fun j : Fin (2 + 1) => ((Fine ^ (j : ℕ)) U : Phys))
local notation "Src" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "B" =>
  p4Q2PZ37R_originalWilsonThreeGramLower
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- Fully authentic original Wilson posterior mass carries a positive
model-dependent fraction of the explicit PZ37T physical Gram floor
for EVERY three-mode coefficient vector. The GL posterior and Gram
constants remain distinct; neither is assumed volume-uniform. -/
theorem p4Q2PZ37U_allFiniteSmallFine_originalPosteriorMass_explicitGramFloor
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < B ∧
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          ∀ a : Fin (2 + 1) → ℝ,
            (c * B) * (∑ j : Fin (2 + 1), (a j) ^ 2) ≤
              Mass (Src a) (Finset.univ : Finset Link) ∧
            Mass (Src a) (Finset.univ : Finset Link) ≤
              C * ‖Src a‖ ^ 2) := by
  obtain ⟨delta, hdelta, hPhysical⟩ :=
    p4Q2PZ37T_allFiniteSmallFine_originalPhysicalSynthesis_quadratic_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨hB, hQuadratic⟩ := hPhysical hFine hSmall
  obtain ⟨c, C, hc, hcC, hMass⟩ :=
    p4Q2PZ37U_allFinite_allDepth_originalPosteriorMass_physicalNorm_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen e left₀
  refine ⟨hB, c, C, hc, hcC, ?_⟩
  intro a
  have hSource : Src a = (p4Q2AD_realFiniteSynthesis Krylov) a := rfl
  have hLower :
      B * (∑ j : Fin (2 + 1), (a j) ^ 2) ≤ ‖Src a‖ ^ 2 := by
    rw [hSource]
    exact hQuadratic a
  have hScaled := mul_le_mul_of_nonneg_left hLower hc.le
  constructor
  · calc
      (c * B) * (∑ j : Fin (2 + 1), (a j) ^ 2) =
          c * (B * (∑ j : Fin (2 + 1), (a j) ^ 2)) := by ring
      _ ≤ c * ‖Src a‖ ^ 2 := hScaled
      _ ≤ Mass (Src a) (Finset.univ : Finset Link) := (hMass a).1
  · exact (hMass a).2

end ThreeModeQuantitativePosterior
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37U_allFinite_allDepth_originalSourceKernel_eq_GIJoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37U_allFinite_allDepth_originalPosteriorMass_physicalNorm_compare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37U_allFiniteSmallFine_originalPosteriorMass_explicitGramFloor
