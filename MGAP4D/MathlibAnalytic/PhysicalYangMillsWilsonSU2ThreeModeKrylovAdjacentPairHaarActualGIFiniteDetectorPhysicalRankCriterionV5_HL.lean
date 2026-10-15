import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIFiniteContextKernelCertificateV5_HK
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# P4-Q2-HL: finite genuine GI detector rank criterion for physical separation

HK proves that finitely many ACTUAL SU(2) physical link / boundary-pair
two-interacting-Wilson-posterior GI evaluations capture the entire original
GI common kernel K of actual fine right Krylov coefficients.

HJ builds the distinct physical source synthesis S and proves ker S <= K.
In a finite-dimensional coefficient space, rank-nullity converts the still
open physical source separation question into an EXACT FINITE RANK TEST:

  ker S = ker D_F  IFF  finrank(range S) = finrank(range D_F).

A strict shortfall of GI detector rank relative to the TRUE physical
source rank is equivalent to existence of an actual nonzero physical
Haar-L² source that every selected Wilson GI evaluation fails to detect.

This is a necessary-and-sufficient test, NOT a proof of equal ranks,
nor a computation of the actual Wilson posterior matrix. In particular
it does not remove the source separation obstruction or establish
volume-uniform frame bounds, H1-C3 or continuum Yang-Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2700000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

/-- Under a KNOWN inclusion of kernels, rank-nullity makes kernel
equality equivalent to equality of finite-dimensional image ranks.
No finite dimensionality is needed for either target. -/
theorem p4Q2HL_abstract_kernel_eq_iff_range_finrank_eq
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] G)
    (hKerLe : S.ker ≤ D.ker) :
    S.ker = D.ker ↔
      Module.finrank ℝ ↥S.range = Module.finrank ℝ ↥D.range := by
  have hS := LinearMap.finrank_range_add_finrank_ker S
  have hD := LinearMap.finrank_range_add_finrank_ker D
  constructor
  · intro hEq
    rw [← hEq] at hD
    omega
  · intro hRank
    have hKernelFinrank :
        Module.finrank ℝ ↥S.ker = Module.finrank ℝ ↥D.ker := by
      omega
    exact Submodule.eq_of_le_of_finrank_eq hKerLe hKernelFinrank

/-- The detected image cannot have greater dimension than the
true physical source image when its kernel includes the source kernel. -/
theorem p4Q2HL_abstract_detector_rank_le_source_rank
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] G)
    (hKerLe : S.ker ≤ D.ker) :
    Module.finrank ℝ ↥D.range ≤ Module.finrank ℝ ↥S.range := by
  have hS := LinearMap.finrank_range_add_finrank_ker S
  have hD := LinearMap.finrank_range_add_finrank_ker D
  have hKerDim := Submodule.finrank_mono hKerLe
  omega

/-- A strict detector rank loss relative to the physical source rank
is EQUIVALENT to a concrete nonzero source killed by that detector.
This uses no surrogate posterior and no source-frame assumption. -/
theorem p4Q2HL_abstract_invisible_source_iff_strict_rank_loss
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (D : E →ₗ[ℝ] G)
    (hKerLe : S.ker ≤ D.ker) :
    (∃ a : E, S a ≠ 0 ∧ D a = 0) ↔
      Module.finrank ℝ ↥D.range < Module.finrank ℝ ↥S.range := by
  have hRankLe := p4Q2HL_abstract_detector_rank_le_source_rank S D hKerLe
  have hKerRank := p4Q2HL_abstract_kernel_eq_iff_range_finrank_eq S D hKerLe
  constructor
  · rintro ⟨a, haS, haD⟩
    have hKerNe : S.ker ≠ D.ker := by
      intro hEq
      have haInD : a ∈ D.ker := (LinearMap.mem_ker).mpr haD
      have haInS : a ∈ S.ker := by rwa [hEq]
      exact haS ((LinearMap.mem_ker).mp haInS)
    have hRankNe : Module.finrank ℝ ↥S.range ≠ Module.finrank ℝ ↥D.range := by
      intro hEq
      exact hKerNe (hKerRank.mpr hEq)
    exact lt_of_le_of_ne hRankLe (Ne.symm hRankNe)
  · intro hStrict
    have hKerNe : S.ker ≠ D.ker := by
      intro hEq
      have hRankEq := hKerRank.mp hEq
      omega
    have hExists : ∃ a : E, a ∈ D.ker ∧ a ∉ S.ker := by
      by_contra hNone
      have hReverse : D.ker ≤ S.ker := by
        intro a haD
        by_contra haNotS
        exact hNone ⟨a, haD, haNotS⟩
      exact hKerNe (le_antisymm hKerLe hReverse)
    obtain ⟨a, haD, haNotS⟩ := hExists
    refine ⟨a, ?_, (LinearMap.mem_ker).mp haD⟩
    intro haS
    exact haNotS ((LinearMap.mem_ker).mpr haS)

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Pair" => Cfg × Cfg
local notation "Context" => Link × Pair
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Every selected original finite GI context family with exact joint
kernel has the genuine physical source kernel included in its kernel. -/
theorem p4Q2HL_actualRight_sourceKernel_le_exactFiniteGIKernel
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (PhysicalSource).ker ≤ (FiniteDetector s).ker := by
  have hLe :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] at hLe
  simpa only [hExact] using hLe

/-- For an EXACT finite genuine Wilson GI kernel certificate:
physical source separation holds IFF physical and GI detector image
ranks coincide; the latter is the rank of a finite real detector. -/
theorem p4Q2HL_actualRight_sourceSeparation_iff_finiteGIRankEq
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (PhysicalSource).ker = JointKernel ↔
      Module.finrank ℝ ↥(PhysicalSource).range =
      Module.finrank ℝ ↥(FiniteDetector s).range := by
  have hLe :=
    p4Q2HL_actualRight_sourceKernel_le_exactFiniteGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hExact
  have hRank := p4Q2HL_abstract_kernel_eq_iff_range_finrank_eq
    (PhysicalSource) (FiniteDetector s) hLe
  simpa only [hExact] using hRank

/-- Rank deficiency of the true finite Wilson detector relative
to the actual physical source synthesis is exactly the existence of
a genuine nonzero signed physical Haar-L² source annihilated by
the entire selected finite family of two-posterior GI evaluations. -/
theorem p4Q2HL_actualRight_finiteGIRankLoss_iff_invisiblePhysicalSource
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (Module.finrank ℝ ↥(FiniteDetector s).range <
      Module.finrank ℝ ↥(PhysicalSource).range) ↔
      ∃ a : Coeff, PhysicalSource a ≠ 0 ∧
        FiniteDetector s a = 0 := by
  have hLe :=
    p4Q2HL_actualRight_sourceKernel_le_exactFiniteGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hExact
  exact (p4Q2HL_abstract_invisible_source_iff_strict_rank_loss
    (PhysicalSource) (FiniteDetector s) hLe).symm

/-- Extract a FINITE genuine Wilson context detector whose image
rank determines precisely whether the actual physical-source
separation theorem holds. This does NOT evaluate the rank. -/
theorem p4Q2HL_actualRight_exists_finiteGI_sourceSeparation_rankCriterion :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      ((PhysicalSource).ker = JointKernel ↔
        Module.finrank ℝ ↥(PhysicalSource).range =
        Module.finrank ℝ ↥(FiniteDetector s).range) ∧
      ((Module.finrank ℝ ↥(FiniteDetector s).range <
          Module.finrank ℝ ↥(PhysicalSource).range) ↔
        ∃ a : Coeff, PhysicalSource a ≠ 0 ∧ FiniteDetector s a = 0) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_, ?_⟩
  · exact p4Q2HL_actualRight_sourceSeparation_iff_finiteGIRankEq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs
  · exact p4Q2HL_actualRight_finiteGIRankLoss_iff_invisiblePhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_abstract_kernel_eq_iff_range_finrank_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_abstract_detector_rank_le_source_rank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_abstract_invisible_source_iff_strict_rank_loss
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_actualRight_sourceKernel_le_exactFiniteGIKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_actualRight_sourceSeparation_iff_finiteGIRankEq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_actualRight_finiteGIRankLoss_iff_invisiblePhysicalSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HL_actualRight_exists_finiteGI_sourceSeparation_rankCriterion
