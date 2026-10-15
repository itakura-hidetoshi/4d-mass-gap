import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointBoundaryContinuityV5_HI
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# P4-Q2-HJ: actual continuous GI detector, finite-rank frame, source obstruction

HI proves joint continuity of the authentic difference of the two interacting
Wilson posterior expectations for every physical Haar-L² source. HF proves
real finite Krylov coefficient linearity and HG constructs the genuine
all-link/all-context common kernel K of those functionals.

This file assembles the ACTUAL (not independently-Haar substituted)
continuous GI detector as a real linear map

  Phi : R^(r+1) -> (actual physical links -> C(pair SU(2) boundaries, R)),

and proves ker Phi = HG's K. For frozen beta>0, original GL detection
mass is zero iff Phi vanishes.

By finite-dimensional linear normed-space theory, a complement W of this
kernel exists and the restriction Phi|W is anti-Lipschitz with a positive
constant. This is a genuine finite-dimensional detector FRAME CERTIFICATE
on the DETECTABLE quotient, with no assertion of a uniform lower bound
in H,n,r, or lattice spacing. The complement and constant are noncanonical.

The TRUE signed source synthesis S is also constructed as a separate
linear map. We prove ker S <= ker Phi and an exact separation dichotomy:
either these two physical kernels coincide, or a NONZERO actual physical
source is invisible to EVERY original GI Wilson posterior detector.
Neither alternative is asserted by itself. In particular, this theorem
does NOT assume GI anchor nonvanishing or prove a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 850000

local instance p4Q2HJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HJ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Any real linear map on a finite-dimensional normed space has a
complement to its kernel on which it has a positive anti-Lipschitz
constant. This is the mathematically correct quotient-frame statement,
not a claim of injectivity on all of the coefficient space. -/
theorem p4Q2HJ_abstract_finiteDetector_complement_frame
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] F) :
    ∃ W : Submodule ℝ E, IsCompl L.ker W ∧
      ∃ c : NNReal, 0 < c ∧
        AntilipschitzWith c (fun w : W => L (w : E)) := by
  obtain ⟨W, hCompl⟩ := L.ker.exists_isCompl
  let T : W →ₗ[ℝ] F := L.comp W.subtype
  have hInjective : Function.Injective T := by
    intro x y hxy
    have hLxy : L (x : E) = L (y : E) := by
      simpa only [T, LinearMap.comp_apply, Submodule.subtype_apply] using hxy
    have hK : (x : E) - (y : E) ∈ L.ker := by
      change L ((x : E) - (y : E)) = 0
      rw [map_sub, hLxy, sub_self]
    have hW : (x : E) - (y : E) ∈ W := W.sub_mem x.property y.property
    have hBot : (x : E) - (y : E) ∈ (⊥ : Submodule ℝ E) := by
      rw [← hCompl.inf_eq_bot]
      exact ⟨hK, hW⟩
    have hZero : (x : E) - (y : E) = 0 := by simpa using hBot
    exact Subtype.ext (sub_eq_zero.mp hZero)
  obtain ⟨c, hc, hFrame⟩ :=
    (LinearMap.injective_iff_antilipschitz T).mp hInjective
  refine ⟨W, hCompl, c, hc, ?_⟩
  simpa only [T, LinearMap.comp_apply, Submodule.subtype_apply] using hFrame

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Pair" => Cfg × Cfg
local notation "Detector" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Every ACTUAL GI modal evaluation defines a genuine continuous real
function of the entire physical SU(2) pair boundary. -/
theorem p4Q2HJ_actualRightGIModalEvaluation_continuous
    (a : Coeff) (e : Link) :
    Continuous (fun z : Pair => (Detector e z) a) := by
  have hGI :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
  have hEq :
      (fun z : Pair => (Detector e z) a) =
      (fun z : Pair =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z) := by
    funext z
    exact (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).symm
  rw [hEq]
  exact hGI

/-- The TRUE signed finite right-Krylov coefficient to physical Haar-L²
source synthesis is a real linear map for arbitrary nonnegative fine beta.
No independence or frame bound for the actual modes is assumed. -/
noncomputable def p4Q2HJ_actualRightPhysicalSourceSynthesis :
    Coeff →ₗ[ℝ] Phys where
  toFun a := ∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)
  map_add' := by
    intro a b
    change (∑ j : Fin (r + 1), (a j + b j) • RightFactor n (j : ℕ)) =
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) +
      (∑ j : Fin (r + 1), b j • RightFactor n (j : ℕ))
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    change (∑ j : Fin (r + 1), (c * a j) • RightFactor n (j : ℕ)) =
      c • (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
    simp only [mul_smul, Finset.smul_sum]

/-- The ORIGINAL Wilson two-interacting-posterior GI detector assembled
into an honest continuous-function-valued REAL LINEAR MAP. Its output at
each real physical link retains the ENTIRE original boundary context. -/
noncomputable def p4Q2HJ_actualRightGIContinuousDetector :
    Coeff →ₗ[ℝ] (Link → C(Pair, ℝ)) where
  toFun a e :=
    ⟨(fun z : Pair => (Detector e z) a),
      p4Q2HJ_actualRightGIModalEvaluation_continuous
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e⟩
  map_add' := by
    intro a b
    funext e
    apply ContinuousMap.ext
    intro z
    change (Detector e z) (a + b) = (Detector e z) a + (Detector e z) b
    exact map_add (Detector e z) a b
  map_smul' := by
    intro c a
    funext e
    apply ContinuousMap.ext
    intro z
    change (Detector e z) (c • a) = c • (Detector e z) a
    exact map_smul (Detector e z) c a

/-- Evaluating the assembled continuous GI detector is EXACTLY HF's
literal modal linear map, hence the original physical expectation gap. -/
theorem p4Q2HJ_actualRightGIContinuousDetector_apply
    (a : Coeff) (e : Link) (z : Pair) :
    (p4Q2HJ_actualRightGIContinuousDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e) z = (Detector e z) a := rfl

/-- The kernel of the ACTUAL continuous-function GI detector is exactly
HG's all-link/all-context true Wilson expectation-gap submodule. -/
theorem p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel :
    (p4Q2HJ_actualRightGIContinuousDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).ker =
    p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r := by
  ext a
  constructor
  · intro ha
    have hZero :
        p4Q2HJ_actualRightGIContinuousDetector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a = 0 := (LinearMap.mem_ker).mp ha
    apply (p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mpr
    intro e z
    have hz : (Detector e z) a = 0 := by
      have hh := congrArg (fun v : Link → C(Pair, ℝ) => v e z) hZero
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hh
    exact (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).trans hz
  · intro ha
    apply (LinearMap.mem_ker).mpr
    funext e
    apply ContinuousMap.ext
    intro z
    have hAll := (p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mp ha
    have hGI := hAll e z
    have hz : (Detector e z) a = 0 :=
      (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e z).symm.trans hGI
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hz

/-- Original true signed physical-source zero implies vanishing of the
assembled continuous GI detector, with no converse assumption. -/
theorem p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel :
    (p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).ker ≤
    (p4Q2HJ_actualRightGIContinuousDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).ker := by
  intro a ha
  rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel]
  apply p4Q2HG_actualSource_zero_mem_GIJointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  exact (LinearMap.mem_ker).mp ha

/-- SCIENTIFIC OBSTRUCTION DICHOTOMY: either the genuine physical
source synthesis kernel equals the GI detector kernel, or a nonzero
actual signed physical Haar-L² source is invisible at EVERY original
interacting two-Wilson-posterior boundary and link. This theorem does
not decide which branch holds. -/
theorem p4Q2HJ_actualRightSourceSeparation_or_invisiblePhysicalWitness :
    (p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).ker =
    (p4Q2HJ_actualRightGIContinuousDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).ker ∨
    ∃ a : Coeff,
      p4Q2HJ_actualRightPhysicalSourceSynthesis
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a ≠ 0 ∧
      p4Q2HJ_actualRightGIContinuousDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a = 0 := by
  let S := p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  let Phi := p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hInclude : S.ker ≤ Phi.ker :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  by_cases hEq : S.ker = Phi.ker
  · exact Or.inl hEq
  · right
    have hWitness : ∃ a : Coeff, a ∈ Phi.ker ∧ a ∉ S.ker := by
      by_contra hNone
      have hReverse : Phi.ker ≤ S.ker := by
        intro a ha
        by_contra hNot
        exact hNone ⟨a, ha, hNot⟩
      exact hEq (le_antisymm hInclude hReverse)
    obtain ⟨a, haPhi, haNotS⟩ := hWitness
    refine ⟨a, ?_, ?_⟩
    · intro hZero
      exact haNotS ((LinearMap.mem_ker).mpr hZero)
    · exact (LinearMap.mem_ker).mp haPhi

/-- At frozen beta>0, the *original* Wilson GL two-posterior
gap-square detection mass has zero-locus precisely the kernel of the
ACTUAL continuous detector (not the physical source kernel). -/
theorem p4Q2HJ_actualRightGLMass_zero_iff_continuousDetector_zero
    (hFrozen : 0 < beta n) (a : Coeff) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) = 0 ↔
    p4Q2HJ_actualRightGIContinuousDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a = 0 := by
  rw [p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a]
  rw [← p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  exact LinearMap.mem_ker

/-- The detector image is finite-dimensional, with exact rank-nullity
relative to HG's true physical GI common kernel, NOT source synthesis. -/
theorem p4Q2HJ_actualRightGIContinuousDetector_finrank_identity :
    Module.finrank ℝ
      ↥(p4Q2HJ_actualRightGIContinuousDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r).range +
    Module.finrank ℝ
      ↥(p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) = r + 1 := by
  let Phi := p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hRank := LinearMap.finrank_range_add_finrank_ker Phi
  rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] at hRank
  have hCoeffDim : Module.finrank ℝ (Fin (r + 1) → ℝ) = r + 1 := by
    simp
  rw [hCoeffDim] at hRank
  simpa only [Phi] using hRank

/-- FINITE-DETECTOR FRAME: without assuming a nonzero original GI anchor,
there exists a (possibly zero-dimensional) real complement W to the
original GI joint kernel, and a strictly positive constant c for which
the actual continuous-function-valued Wilson detector is anti-Lipschitz
on W. No physical-source separation or volume- or spacing-uniformity follows. -/
theorem p4Q2HJ_actualRightGIContinuousDetector_complement_frame :
    ∃ W : Submodule ℝ Coeff,
      IsCompl
        (p4Q2HG_actualRightGIJointModalKernel
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) W ∧
      ∃ c : NNReal, 0 < c ∧
        AntilipschitzWith c (fun w : W =>
          p4Q2HJ_actualRightGIContinuousDetector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r (w : Coeff)) := by
  have hFrame :=
    p4Q2HJ_abstract_finiteDetector_complement_frame
      (p4Q2HJ_actualRightGIContinuousDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
  simpa only [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] using hFrame

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_abstract_finiteDetector_complement_frame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGIModalEvaluation_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightPhysicalSourceSynthesis
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGIContinuousDetector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightSourceSeparation_or_invisiblePhysicalWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGLMass_zero_iff_continuousDetector_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGIContinuousDetector_finrank_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HJ_actualRightGIContinuousDetector_complement_frame
