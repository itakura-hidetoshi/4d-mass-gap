import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIContinuousDetectorComplementFrameV5_HJ
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# P4-Q2-HK: a finite set of ACTUAL Wilson GI contexts detects the entire joint kernel

HJ constructs a continuous-function-valued real GI map Phi from the genuine
fine-right Krylov coefficient space and identifies ker Phi with HG's common
kernel K at ALL physical links and ALL SU(2) pair boundary configurations.

A finite-dimensional real coefficient space is an Artinian module. The pinned
mathlib Finset.exists_inf_eq_iInf theorem therefore extracts a FINITE set
of ACTUAL (physical link, full pair boundary) contexts whose original GI
kernel intersection equals the full K. No synthetic posterior, replacement
measure, frame hypothesis, or discrete approximation of SU(2) is introduced.

Assemble the actual modal GI scalar evaluations at these finitely many
genuine contexts into an explicit real linear map D_s to s -> Real.
Its kernel is exactly K, even when fine coupling beta(n+1)=0 and Krylov
coefficients are linearly dependent. On a complement to K, mathlib gives a
positive finite-dimensional anti-Lipschitz certificate for the FINITE
detector. This constant and the selected contexts may depend on H,n,r,beta.

The remaining physical obstruction ker(S) versus ker(Phi) is not erased:
either the finite contexts already separate all true physical sources in
the Krylov span or a nonzero genuine physical source is invisible at each
selected original two-posterior Wilson context. This is a logical
dichotomy, not an unconditional assertion of source separation.

No bound on the cardinality of the selected finite set, positive
GL-integral mass coefficient, volume uniformity, physical scale
reconstruction, continuum Hamiltonian, or Yang-Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2HK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HK_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- An arbitrary family of real submodules of an ARTINIAN coefficient
module has the same common kernel/intersection as some finite subfamily.
This is pinned mathlib's finite-infimum extraction, not an assumed
finite set of physical context points. -/
theorem p4Q2HK_artinian_submodules_finite_inf
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [IsArtinian ℝ E] (L : I → Submodule ℝ E) :
    ∃ s : Finset I, (⨅ i ∈ s, L i) = ⨅ i, L i := by
  obtain ⟨s, hs⟩ := Finset.exists_inf_eq_iInf L
  exact ⟨s, by simpa only [Finset.inf_eq_iInf] using hs⟩

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
local notation "Context" => Link × Pair
local notation "Detector" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "PhysicalSynthesis" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "ContinuousDetector" =>
  p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- There are finitely many GENUINE physical link / pair-boundary contexts
whose original two-interacting-Wilson-posterior modal kernels intersect to
the entire original all-boundary GI common kernel, at any fine beta>=0. -/
theorem p4Q2HK_actualRightGIJointKernel_finiteContexts :
    ∃ s : Finset Context,
      (⨅ x ∈ s, (Detector x.1 x.2).ker) = JointKernel := by
  haveI : IsArtinian ℝ Coeff := inferInstance
  obtain ⟨s, hs⟩ :=
    p4Q2HK_artinian_submodules_finite_inf
      (E := Coeff) (fun x : Context => (Detector x.1 x.2).ker)
  refine ⟨s, ?_⟩
  rw [hs]
  change (⨅ x : Context, (Detector x.1 x.2).ker) =
    (⨅ e : Link, ⨅ z : Pair, (Detector e z).ker)
  ext a
  simp only [Submodule.mem_iInf]
  exact ⟨(fun h e z => h (e, z)), (fun h ⟨e, z⟩ => h e z)⟩

/-- An explicit FINITE real linear detector built only from the original
two-Wilson-posterior GI expectation gaps evaluated at true physical
link-boundary context points (rather than a surrogate probability law). -/
noncomputable def p4Q2HK_actualRightFiniteGIContextDetector
    (s : Finset Context) : Coeff →ₗ[ℝ] (s → ℝ) where
  toFun a p := (Detector p.1.1 p.1.2) a
  map_add' := by
    intro a b
    funext p
    exact map_add (Detector p.1.1 p.1.2) a b
  map_smul' := by
    intro c a
    funext p
    exact map_smul (Detector p.1.1 p.1.2) c a

/-- Kernel membership of the concrete finite detector is precisely
vanishing of every original GI expectation-gap evaluation selected by s. -/
theorem p4Q2HK_actualRightFiniteGIContextDetector_mem_ker_iff
    (s : Finset Context) (a : Coeff) :
    a ∈ (p4Q2HK_actualRightFiniteGIContextDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).ker ↔
    ∀ x ∈ s, (Detector x.1 x.2) a = 0 := by
  constructor
  · intro ha x hx
    have hZero := (LinearMap.mem_ker).mp ha
    have hp := congrArg (fun g : s → ℝ => g ⟨x, hx⟩) hZero
    simpa [p4Q2HK_actualRightFiniteGIContextDetector] using hp
  · intro h
    apply (LinearMap.mem_ker).mpr
    funext x
    change (Detector x.1.1 x.1.2) a = 0
    exact h x.1 x.2

/-- The entire genuine all-context Wilson GI detector kernel can be
captured by a FINITE real-vector-valued detector at actual contexts. -/
theorem p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel :
    ∃ s : Finset Context,
      (p4Q2HK_actualRightFiniteGIContextDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).ker = JointKernel := by
  obtain ⟨s, hs⟩ := p4Q2HK_actualRightGIJointKernel_finiteContexts
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, ?_⟩
  ext a
  rw [p4Q2HK_actualRightFiniteGIContextDetector_mem_ker_iff,
    ← hs]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/-- At frozen beta>0, vanishing of the original GL physical gap-square
mass is equivalent to the vanishing of a FINITE set of true GI context
evaluations; no positivity of the physical-source synthesis is assumed. -/
theorem p4Q2HK_actualRightGLMass_zero_iff_finiteGIContextDetector
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context, ∀ a : Coeff,
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n) (PhysicalSynthesis a)
        (Finset.univ : Finset Link) = 0 ↔
      p4Q2HK_actualRightFiniteGIContextDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s a = 0 := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, fun a => ?_⟩
  change p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ))
      (Finset.univ : Finset Link) = 0 ↔
    p4Q2HK_actualRightFiniteGIContextDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s a = 0
  rw [p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a, ← hs]
  exact LinearMap.mem_ker

/-- The finite true-Wilson detector has a positive norm stability
constant on a complement of the common GI kernel, with no physical
source-frame or spatial-uniformity assumptions. This complements HJ's
continuous-function normed codomain by an explicit finite real vector. -/
theorem p4Q2HK_actualRightFiniteGIContextDetector_complement_frame :
    ∃ s : Finset Context,
      (p4Q2HK_actualRightFiniteGIContextDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).ker = JointKernel ∧
      ∃ W : Submodule ℝ Coeff,
        IsCompl JointKernel W ∧
        ∃ c : NNReal, 0 < c ∧
          AntilipschitzWith c (fun w : W =>
            p4Q2HK_actualRightFiniteGIContextDetector
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r s (w : Coeff)) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  obtain ⟨W, hCompl, c, hc, hLip⟩ :=
    p4Q2HJ_abstract_finiteDetector_complement_frame
      (p4Q2HK_actualRightFiniteGIContextDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s)
  refine ⟨s, hs, W, ?_, c, hc, hLip⟩
  simpa only [hs] using hCompl

/-- Scientific source-separation obstruction at the finite certificate:
either the true physical-source synthesis and finite GI detector have
identical kernels, or an actual nonzero physical source is annihilated
at ALL selected original Wilson GI contexts. The selection also
detects the entire infinite all-link/all-boundary GI common kernel. -/
theorem p4Q2HK_actualRightFiniteGIContext_sourceSeparation_or_obstruction :
    ∃ s : Finset Context,
      (p4Q2HK_actualRightFiniteGIContextDetector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).ker = JointKernel ∧
      ((PhysicalSynthesis.ker =
        (p4Q2HK_actualRightFiniteGIContextDetector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r s).ker) ∨
       ∃ a : Coeff, PhysicalSynthesis a ≠ 0 ∧
        p4Q2HK_actualRightFiniteGIContextDetector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r s a = 0) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  rcases p4Q2HJ_actualRightSourceSeparation_or_invisiblePhysicalWitness
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r with
    hSep | ⟨a, haNonzero, haInvisible⟩
  · left
    simpa only [hs, p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] using hSep
  · right
    refine ⟨a, haNonzero, ?_⟩
    apply (LinearMap.mem_ker).mp
    rw [hs]
    rw [← p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel]
    exact (LinearMap.mem_ker).mpr haInvisible

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_artinian_submodules_finite_inf
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightGIJointKernel_finiteContexts
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightFiniteGIContextDetector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightFiniteGIContextDetector_mem_ker_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightGLMass_zero_iff_finiteGIContextDetector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightFiniteGIContextDetector_complement_frame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HK_actualRightFiniteGIContext_sourceSeparation_or_obstruction
