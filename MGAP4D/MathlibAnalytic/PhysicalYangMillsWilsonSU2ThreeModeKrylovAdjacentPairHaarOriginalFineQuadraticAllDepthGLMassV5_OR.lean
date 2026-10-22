import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineQuadraticCollapseAllDepthV5_OQ
import Mathlib.Tactic

/-!
# P4-Q2-OR — true two-posterior Wilson GL mass positivity at ALL depths on genuine quadratic-collapse branch

OQ #5809 proves a genuine ORIGINAL normalized Wilson fine transfer
quadratic-orbit dichotomy for positive frozen coupling and sufficiently
small positive fine coupling on each finite spatial SU(2) lattice.

Here the genuine GL two-INTERACTING-posterior expectation-gap-square
mass, divided by the actual positive posterior density-contrast
variance, is proved nonnegative directly from the ORIGINAL ratio
integral at each real link/context.

Combining HJ's original GL-mass zero-locus theorem with OQ's
ALL-depth source/GI kernel equality, we prove, in the genuine
Schur-physical-source-zero branch, for EVERY finite right-Krylov depth:

  TrueOriginalWilsonGLMass(S_r a)=0  <-> S_r a=0.
  S_r a != 0 -> TrueOriginalWilsonGLMass(S_r a)>0.

The final UNCONDITIONAL finite-H small-positive-fine disjunction is:
either ALL finite-depth genuine physical sources have strict positive
original two-posterior GL mass whenever physically nonzero,
or the SAME OO depth-two genuine Schur physical Hilbert source is nonzero.

The alternative physical source is not asserted to be detected by a
third genuine GI receiver. No volume- or spacing-uniform GL floor, arbitrary
positive fine, endpoint, H1-C3 or continuum Yang--Mills mass gap is
claimed. Frozen/fine Wilson couplings remain distinct. No
Dobrushin, independent-Haar surrogate, arbitrary rank axiom, sorry,
admit or new unproved axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonPhysicalGLMass
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
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

 /-- The unchanged true signed two-posterior Wilson link-mass is
nonnegative because the numerator is a REAL signed expectation gap
SQUARED and the denominator is the strictly positive true
interacting Wilson density-contrast Haar L2 variance (FX). -/
theorem p4Q2OR_originalTwoPosteriorWilson_linkMass_nonneg
    (hFrozen : 0 < beta n) (f : Phys) (e : Link) :
    0 ≤ p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
      Hn (beta n) (hbeta n) f e := by
  unfold p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  apply integral_nonneg
  intro z
  have hDen :
      0 ≤ p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        Hn (beta n) (hbeta n) z.2 e :=
    le_of_lt (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      Hn (beta n) hFrozen z.2 e)
  exact div_nonneg (sq_nonneg _) hDen

/-- The ACTUAL full finite spatial-link original Wilson two-posterior
GL mass is nonnegative on EVERY true Gauss-law physical source,
without a surrogate Haar posterior or a hypothetical source rank. -/
theorem p4Q2OR_originalTwoPosteriorWilson_fullMass_nonneg
    (hFrozen : 0 < beta n) (f : Phys) :
    0 ≤ Mass f (Finset.univ : Finset Link) := by
  unfold p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  apply Finset.sum_nonneg
  intro e _he
  exact p4Q2OR_originalTwoPosteriorWilson_linkMass_nonneg
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen f e

/-- On any true Wilson right-Krylov depth r where the physical
synthesis and entire original interacting two-posterior GI detector
kernels are proved IDENTICAL, the original GL mass zero-locus
is EXACTLY the zero physical Hilbert source. -/
theorem p4Q2OR_originalAllDepth_mass_zero_iff_physicalZero_of_kernelEquality
    (hFrozen : 0 < beta n) (r : ℕ)
    (a : Fin (r + 1) → ℝ)
    (hEq : (S r).ker = (Full r).ker) :
    Mass (S r a) (Finset.univ : Finset Link) = 0 ↔
      S r a = 0 := by
  change p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
    (∑ j : Fin (r + 1),
      a j • physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ))
    (Finset.univ : Finset Link) = 0 ↔ S r a = 0
  rw [p4Q2HJ_actualRightGLMass_zero_iff_continuousDetector_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a]
  constructor
  · intro hPhi
    have hMem : a ∈ (Full r).ker := (LinearMap.mem_ker).mpr hPhi
    rw [← hEq] at hMem
    exact (LinearMap.mem_ker).mp hMem
  · intro hSource
    have hMem : a ∈ (S r).ker := (LinearMap.mem_ker).mpr hSource
    rw [hEq] at hMem
    exact (LinearMap.mem_ker).mp hMem

/-- Positive true GI/GL mass for EVERY nonzero ACTUAL physical
right-Krylov source in any proved physical/all-context GI kernel
equality branch. Its positive value depends on the real finite
Wilson model, not on an invented rank or a uniform lower bound. -/
theorem p4Q2OR_originalAllDepth_mass_pos_of_kernelEquality
    (hFrozen : 0 < beta n) (r : ℕ)
    (a : Fin (r + 1) → ℝ)
    (hEq : (S r).ker = (Full r).ker)
    (hSource : S r a ≠ 0) :
    0 < Mass (S r a) (Finset.univ : Finset Link) := by
  have hNonneg :
      0 ≤ Mass (S r a) (Finset.univ : Finset Link) :=
    p4Q2OR_originalTwoPosteriorWilson_fullMass_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen (S r a)
  have hIff :=
    p4Q2OR_originalAllDepth_mass_zero_iff_physicalZero_of_kernelEquality
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen r a hEq
  rcases lt_or_eq_of_le hNonneg with hPos | hZero
  · exact hPos
  · exact False.elim (hSource (hIff.mp hZero.symm))

/-- Original Wilson quadratic Schur PHYSICAL collapse forces exact
true GL-mass/source zero-locus equivalence at ALL finite depths.
The hypothesis is an actual physical source equation, not a
surrogate rank axiom. -/
theorem p4Q2OR_actualQuadraticSchurZero_allDepth_massZero_iff_sourceZero
    (hFrozen : 0 < beta n) (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0)
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    Mass (S r a) (Finset.univ : Finset Link) = 0 ↔
      S r a = 0 := by
  have hEq :=
    p4Q2OQ_actualSchurPhysicalZero_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor hSchur r
  exact p4Q2OR_originalAllDepth_mass_zero_iff_physicalZero_of_kernelEquality
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen r a hEq

/-- On the genuinely quadratic-collapsed physical Wilson fine orbit,
ALL physically nonzero Krylov sources at any finite depth have
STRICTLY POSITIVE TRUE original two-posterior GI/GL mass. -/
theorem p4Q2OR_actualQuadraticSchurZero_allDepth_mass_pos
    (hFrozen : 0 < beta n) (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (hSchur : S 2
      (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) = 0)
    (r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSource : S r a ≠ 0) :
    0 < Mass (S r a) (Finset.univ : Finset Link) := by
  have hEq :=
    p4Q2OQ_actualSchurPhysicalZero_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor hSchur r
  exact p4Q2OR_originalAllDepth_mass_pos_of_kernelEquality
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen r a hEq hSource

/-- UNCONDITIONAL true Wilson finite-H small-positive-fine mass
obstruction dichotomy, with SAME genuine contexts for ALL depths:
either every NONZERO true physical right-Krylov source has positive
original two-posterior GL mass at every finite depth, or the
genuinely synthesized OO depth-two Schur PHYSICAL source is nonzero.

The second branch does NOT establish a third true GI response.
No volume- or scale-uniform lower bound, H1-C3 or continuum result. -/
theorem p4Q2OR_actualSmallFine_allDepth_massPos_or_depthTwoPhysicalObstruction
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (∀ r : ℕ, ∀ a : Fin (r + 1) → ℝ,
          S r a ≠ 0 →
            0 < Mass (S r a) (Finset.univ : Finset Link)) ∨
        S 2 (p4Q2OO_depthTwoSchurResidual
          (M 2 e z) (M 2 e' z')) ≠ 0) := by
  obtain ⟨z, z', delta, hDelta, hDichotomy⟩ :=
    p4Q2OQ_actualSmallFine_allDepthGIKernelEquality_or_depthTwoPhysicalObstruction
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hDelta, ?_⟩
  intro ht hSmall
  rcases hDichotomy ht hSmall with hKernels | hPhysical
  · left
    intro r a hSource
    exact p4Q2OR_originalAllDepth_mass_pos_of_kernelEquality
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen r a (hKernels r) hSource
  · exact Or.inr hPhysical

end OriginalWilsonPhysicalGLMass
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_originalTwoPosteriorWilson_linkMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_originalTwoPosteriorWilson_fullMass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_originalAllDepth_mass_zero_iff_physicalZero_of_kernelEquality
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_originalAllDepth_mass_pos_of_kernelEquality
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_actualQuadraticSchurZero_allDepth_massZero_iff_sourceZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_actualQuadraticSchurZero_allDepth_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OR_actualSmallFine_allDepth_massPos_or_depthTwoPhysicalObstruction
