import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGLPhysicalSourceNormOnGIComplementV5_IG
import Mathlib.Tactic

/-!
# P4-Q2-IJ: exact genuine-Wilson physical-source coercivity criterion

At every finite lattice volume, frozen beta(n)>0, arbitrary finite
right-Krylov depth r and nonnegative fine beta(n+1), the ORIGINAL
interacting-Wilson pair-Haar spatial GL gap-square mass is the quadratic
form of a nonnegative actual detector with joint GI kernel K. The
ACTUAL physical Haar-L² signed-source synthesis S is a separate
linear map; it is already established unconditionally that ker S <= K.

IG proves a finite positive two-sided comparison between the ORIGINAL
Wilson GL mass and the genuine physical SOURCE norm on any real
complement W to K, without claiming ker S=K.

This file proves the mathematically SHARP extension criterion:
  ker S = K
    IFF
  there exist c,C with 0<c<=C and for ALL signed coefficients a,
  c*‖S(a)‖² <= actual OriginalGLMass(S(a)) <= C*‖S(a)‖².

For sufficiency, choose a complement W to K; when K=ker S, every
coefficient has an identical physical source as its component in W,
and the IG finite-model constants extend without loss. For necessity,
a global positive source-norm floor forces every original GL-null
coefficient (equivalently every GI-invisible coefficient) to be an
ACTUALLY vanishing physical Haar-L² source.

HN/HK identify the same criterion with equality of the RANKS of the
genuine finite GI-SOS Gram R and the DISTINCT physical source Gram
Qsrc on an exact finite physical SU(2) context certificate. A
nonzero original physical source invisible to all GI observations
rigorously OBSTRUCTS every possible positive global GL/source floor.

This closes an equivalence/obstruction theorem, NOT the still open
assertion of source separation itself for r>0 with positive fine
coupling. No Dobrushin, independent-Haar conditional, uniform volume
constant, H1-C3, OS Hamiltonian or continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1000000

local instance p4Q2IJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IJ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Context" => Link × Pair
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- Sufficient direction: IF the actual original physical source
kernel equals the true two-interacting-Wilson-posterior GI common
kernel K, the positive model-dependent IG comparison on a complement
to K becomes a positive two-sided comparison on ALL signed physical
sources, with no coefficient independence assumption. -/
theorem p4Q2IJ_originalWilson_sourceSeparation_implies_global_GL_sourceNorm
    (hFrozen : 0 < beta n)
    (hSep : (PhysicalSource).ker = JointKernel) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * ‖PhysicalSource a‖ ^ 2 ≤
          OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
          C * ‖PhysicalSource a‖ ^ 2 := by
  obtain ⟨W, hCompl⟩ := Submodule.exists_isCompl JointKernel
  obtain ⟨c, C, hc, hcC, hComp⟩ :=
    p4Q2IG_actualRight_GL_physicalSourceNorm_comparison_on_GI_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen W hCompl
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  have haTop : a ∈ JointKernel ⊔ W := by
    rw [hCompl.codisjoint.eq_top]
    trivial
  obtain ⟨k, w, hkw⟩ := (Submodule.mem_sup').mp haTop
  have hkS : (k : Coeff) ∈ (PhysicalSource).ker := by
    rw [hSep]
    exact k.property
  have hkZero : PhysicalSource (k : Coeff) = 0 :=
    (LinearMap.mem_ker).mp hkS
  have hSourceEq : PhysicalSource a = PhysicalSource (w : Coeff) := by
    calc
      PhysicalSource a = PhysicalSource ((k : Coeff) + (w : Coeff)) := by
        rw [hkw]
      _ = PhysicalSource (k : Coeff) + PhysicalSource (w : Coeff) := by
        rw [map_add]
      _ = PhysicalSource (w : Coeff) := by
        rw [hkZero, zero_add]
  have hW :
      c * ‖PhysicalSource (w : Coeff)‖ ^ 2 ≤
          OriginalMass (PhysicalSource (w : Coeff))
            (Finset.univ : Finset Link) ∧
      OriginalMass (PhysicalSource (w : Coeff))
          (Finset.univ : Finset Link) ≤
          C * ‖PhysicalSource (w : Coeff)‖ ^ 2 := by
    exact hComp w
  change c * ‖PhysicalSource a‖ ^ 2 ≤
      OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
    OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
      C * ‖PhysicalSource a‖ ^ 2
  rw [hSourceEq]
  exact hW

/-- Necessary direction: a strictly positive original Wilson
GL-mass floor in terms of the ACTUAL physical Haar-L² source norm
forces every true GI-invisible coefficient to synthesize the ZERO
physical source. This uses HI's original interacting Wilson GL
nullity, not a fictitious positive Gram. -/
theorem p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
    (hFrozen : 0 < beta n)
    (c : ℝ) (hc : 0 < c)
    (hFloor : ∀ a : Coeff,
      c * ‖PhysicalSource a‖ ^ 2 ≤
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link)) :
    (PhysicalSource).ker = JointKernel := by
  apply Submodule.ext
  intro a
  constructor
  · intro ha
    apply p4Q2HG_actualSource_zero_mem_GIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
    exact (LinearMap.mem_ker).mp ha
  · intro ha
    have hMassZero :
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) = 0 :=
      (p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen a).mpr ha
    have hBound := hFloor a
    rw [hMassZero] at hBound
    have hSqNonneg : 0 ≤ ‖PhysicalSource a‖ ^ 2 := sq_nonneg _
    have hProdNonneg : 0 ≤ c * ‖PhysicalSource a‖ ^ 2 :=
      mul_nonneg hc.le hSqNonneg
    have hProdZero : c * ‖PhysicalSource a‖ ^ 2 = 0 :=
      le_antisymm hBound hProdNonneg
    have hSqZero : ‖PhysicalSource a‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hProdZero with hcZero | hnZero
      · exact (hc.ne' hcZero).elim
      · exact hnZero
    change PhysicalSource a = 0
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hSqZero)

/-- Exact fixed-original-Wilson equivalence:
  TRUE physical source separation ker S=K
  IFF genuine two-sided GL-mass/source-norm comparison on ALL coefficients.

The existence and positivity of model-dependent constants are proved
conditionally on the real source-kernel equality; that equality itself
is already known in the HZ fine-beta-zero and IB depth-zero cases,
but remains open at r>0 with positive fine coupling. -/
theorem p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_sourceSeparation
    (hFrozen : 0 < beta n) :
    ((PhysicalSource).ker = JointKernel) ↔
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ a : Coeff,
          c * ‖PhysicalSource a‖ ^ 2 ≤
            OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
          OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
            C * ‖PhysicalSource a‖ ^ 2) := by
  constructor
  · intro hSep
    exact p4Q2IJ_originalWilson_sourceSeparation_implies_global_GL_sourceNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hSep
  · rintro ⟨c, _C, hc, _hcC, hBounds⟩
    exact p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen c hc (fun a => (hBounds a).1)

/-- On each exact HK physical SU(2) context certificate, existence
of a genuine global ORIGINAL GL physical-source-norm lower and upper
bound is EQUIVALENT to equality of the ranks of the independently
defined GI-SOS Gram and actual physical Haar-L² source Gram. -/
theorem p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_trueGram_rankEq
    (hFrozen : 0 < beta n)
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * ‖PhysicalSource a‖ ^ 2 ≤
          OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
          C * ‖PhysicalSource a‖ ^ 2) ↔
      (R s).rank = (Qsrc).rank := by
  exact (p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_sourceSeparation
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen).symm.trans
    (p4Q2HN_actualRight_sourceSeparation_iff_GIGram_rank_eq_sourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hExact)

/-- HK supplies actual finite original SU(2) physical contexts
on which the sharp source-norm coercivity/rank certificate is
mathematically exact, without postulating a detector set. -/
theorem p4Q2IJ_originalWilson_exists_exact_trueGram_sourceNorm_criterion
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      ((∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ a : Coeff,
          c * ‖PhysicalSource a‖ ^ 2 ≤
            OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
          OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
            C * ‖PhysicalSource a‖ ^ 2) ↔
        (R s).rank = (Qsrc).rank) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  exact p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_trueGram_rankEq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen s hs

/-- A NONZERO original gauge-invariant Haar-L² physical source
invisible to the entire true two-interacting-Wilson-posterior GI
detector obstructs EVERY positive global GL/source-norm coercivity
constant. Its existence remains an open mathematical alternative
at higher r and positive fine coupling; no witness is invented. -/
theorem p4Q2IJ_originalWilson_invisible_physicalSource_obstructs_global_floor
    (hFrozen : 0 < beta n)
    (a : Coeff) (hInvisible : a ∈ JointKernel)
    (hPhysical : PhysicalSource a ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ b : Coeff,
        c * ‖PhysicalSource b‖ ^ 2 ≤
          OriginalMass (PhysicalSource b) (Finset.univ : Finset Link) := by
  rintro ⟨c, hc, hFloor⟩
  have hSep :=
    p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen c hc hFloor
  have ha : a ∈ (PhysicalSource).ker := by
    rw [hSep]
    exact hInvisible
  exact hPhysical ((LinearMap.mem_ker).mp ha)

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_sourceSeparation_implies_global_GL_sourceNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_sourceSeparation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_global_GL_sourceNorm_iff_trueGram_rankEq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_exists_exact_trueGram_sourceNorm_criterion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IJ_originalWilson_invisible_physicalSource_obstructs_global_floor
