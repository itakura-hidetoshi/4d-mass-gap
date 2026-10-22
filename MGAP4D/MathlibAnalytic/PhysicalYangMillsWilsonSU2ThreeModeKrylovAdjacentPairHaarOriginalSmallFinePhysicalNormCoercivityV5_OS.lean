import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineQuadraticAllDepthGLMassV5_OR
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# P4-Q2-OS — quantitative original Wilson physical-norm separation at fixed finite volume

ON proved unconditional *actual* small-positive-fine injectivity of the
depth-one original normalized Wilson Gauss-law physical source and of
the complete genuine two-interacting-posterior GI detector.  This file
upgrades BOTH to genuine finite-dimensional *norm stability*: for each
fixed small positive fine Wilson coupling there are strictly positive
inverse-Lipschitz constants controlling the two real coefficients by
the true physical Hilbert norm and the full true GI response norm.

For the genuine depth-two source, OP's exact one-dimensional Schur
kernel characterization gives norm stability WHEN (and only when) the
explicit OO physical Schur residual is nonzero.  Combining this with
OR's original two-posterior positive GL mass on the exact quadratic
collapse branch gives a quantitative physical dichotomy:

* every finite-depth nonzero genuine Wilson physical source has
  positive original two-posterior GL mass; OR
* the genuine depth-two source has a strictly positive coefficient
  norm-stability constant.

The second alternative is NOT claimed to hold, and the first does
NOT establish third-mode injectivity.  These constants depend on
volume, frozen and fine coupling; no uniform H/fine/depth bound,
third original GI receiver, endpoint or continuum mass gap follows.

Only the actual Wilson Gauss-law physical source and actual original
interacting two-posterior GI/GL response are used. No rank axiom,
independent-Haar posterior, Dobrushin, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Standard mathlib finite-dimensional lower norm stability, with
no assumed numerical constant: an injective real linear map on a
finite-dimensional normed source admits a positive inverse-Lipschitz
constant.  The proof uses mathlib rather than introducing a physical
rank or coercivity axiom. -/
theorem p4Q2OS_finiteDimensional_injective_normControl
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] F) (hL : Function.Injective L) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ a : E,
      ‖a‖ ≤ (K : ℝ) * ‖L a‖ := by
  obtain ⟨K, hK, hAnti⟩ :=
    (LinearMap.injective_iff_antilipschitz L).mp hL
  refine ⟨K, hK, ?_⟩
  intro a
  have hBound := hAnti.le_mul_dist a 0
  simpa only [map_zero, dist_zero_right] using hBound

section ActualWilsonFiniteVolume
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The actual Gauss-law Hilbert source and complete ORIGINAL GI
detector both have positive norm-separation constants throughout
the proved small-positive-fine depth-one window, for each fixed
finite spatial lattice and coupling. Neither constant is asserted
uniform in the spatial volume or fine coupling. -/
theorem p4Q2OS_actualSmallFine_depthOne_physicalAndGI_normControl
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (∃ K : ℝ≥0, 0 < K ∧ ∀ a : Fin (1 + 1) → ℝ,
          ‖a‖ ≤ (K : ℝ) * ‖S 1 a‖) ∧
        (∃ K : ℝ≥0, 0 < K ∧ ∀ a : Fin (1 + 1) → ℝ,
          ‖a‖ ≤ (K : ℝ) * ‖Full 1 a‖)) := by
  obtain ⟨delta, hdelta, hInject⟩ :=
    p4Q2ON_actualDepthOne_smallFine_fullGI_and_physicalSource_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  obtain ⟨hGI, hPhysical⟩ := hInject ht hsmall
  exact ⟨
    p4Q2OS_finiteDimensional_injective_normControl (S 1) hPhysical,
    p4Q2OS_finiteDimensional_injective_normControl (Full 1) hGI⟩

/-- If the genuinely synthesized OO depth-two PHYSICAL Schur
source is nonzero, the entire true three-mode Wilson source has
a strictly positive inverse-Lipschitz constant on its real coefficient
space. This does NOT assume an arbitrary three-mode rank: it is
derived from OP's proved exact original Schur kernel. -/
theorem p4Q2OS_actualDepthTwo_trueSchurNonzero_physical_normControl
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur :
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ a : Fin (2 + 1) → ℝ,
      ‖a‖ ≤ (K : ℝ) * ‖S 2 a‖ := by
  have hInject : Function.Injective (S 2) :=
    (p4Q2OP_actualDepthTwo_physicalSource_injective_iff_schurNonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor).mpr hSchur
  exact p4Q2OS_finiteDimensional_injective_normControl (S 2) hInject

/-- Actual small-fine quantitative finite-volume dichotomy:
for the SAME genuine two original Wilson GI contexts and positive
fine interval, either all nonzero finite-depth physical Krylov sources
have positive actual original two-posterior GL mass, or the actual
depth-two physical source controls EVERY three-mode coefficient
in norm by a strictly positive inverse-Lipschitz constant.

The statement neither rules out quadratic collapse nor supplies the
still-open physical third-mode nonzero witness. -/
theorem p4Q2OS_actualSmallFine_allDepthGLMass_or_depthTwoNormControl
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (∀ r : ℕ, ∀ a : Fin (r + 1) → ℝ,
          S r a ≠ 0 →
            0 < Mass (S r a) (Finset.univ : Finset Link)) ∨
        (∃ K : ℝ≥0, 0 < K ∧ ∀ a : Fin (2 + 1) → ℝ,
          ‖a‖ ≤ (K : ℝ) * ‖S 2 a‖)) := by
  obtain ⟨z, z', delta, hdelta, hMinor⟩ :=
    p4Q2OO_actualDepthTwo_exists_nonzeroLeadingMinor_smallFine
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hdelta, ?_⟩
  intro ht hsmall
  have hDet := hMinor ht hsmall
  by_cases hSchur :
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0
  · left
    intro r a hNonzero
    exact p4Q2OR_actualQuadraticSchurZero_allDepth_mass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' z z' hDet hSchur r a hNonzero
  · right
    exact p4Q2OS_actualDepthTwo_trueSchurNonzero_physical_normControl
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hDet hSchur

end ActualWilsonFiniteVolume
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OS_finiteDimensional_injective_normControl
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OS_actualSmallFine_depthOne_physicalAndGI_normControl
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OS_actualDepthTwo_trueSchurNonzero_physical_normControl
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OS_actualSmallFine_allDepthGLMass_or_depthTwoNormControl
