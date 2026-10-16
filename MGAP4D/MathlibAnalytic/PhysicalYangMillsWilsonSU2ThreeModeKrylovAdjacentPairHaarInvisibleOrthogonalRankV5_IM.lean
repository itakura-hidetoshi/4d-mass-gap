import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualInvisiblePhysicalSourceSubmoduleV5_IL
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

/-!
# P4-Q2-IM: orthogonal visible physical sector and exact invisible rank criterion

We work ONLY with the original interacting Wilson two-posterior GI detector Phi,
the actual fine-right Krylov signed-source synthesis S, and the physically
invisible submodule I = S(ker Phi) already constructed in IL.

The source span V = range S decomposes *orthogonally within V* as
  V = I + (Iᗮ ∩ V)
with disjoint summands. The orthogonal complement is taken in the true
gauge-invariant Haar-L² physical Hilbert space; it is not replaced by an
artificial coefficient Euclidean metric.

Unconditionally, I=0 iff ker S=ker Phi iff genuine GI and physical-source
ranks agree. These are exact obstruction criteria, NOT a proof that I=0 at
positive fine coupling for r>0. No uniform estimates, independent Haar
posterior, Dobrushin theory, OS reconstruction or continuum gap are claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- General algebraic exactness: the physical image of a detector kernel
vanishes precisely when the source map and detector have identical kernels,
given the already-proved inclusion ker S <= ker Phi. -/
theorem p4Q2IM_abstract_invisibleMap_bot_iff_kernel_eq
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) :
    (Phi.ker.map S = ⊥) ↔ S.ker = Phi.ker := by
  constructor
  · intro hBot
    apply le_antisymm hLe
    intro a ha
    have hMapped : S a ∈ Phi.ker.map S :=
      (Submodule.mem_map).mpr ⟨a, ha, rfl⟩
    rw [hBot] at hMapped
    apply (LinearMap.mem_ker).mpr
    simpa only [Submodule.mem_bot] using hMapped
  · intro hEq
    apply le_antisymm
    · intro f hf
      obtain ⟨a, ha, heq⟩ := (Submodule.mem_map).mp hf
      have haSource : a ∈ S.ker := by rw [hEq]; exact ha
      have hZero : S a = 0 := (LinearMap.mem_ker).mp haSource
      rw [← heq, hZero]
      exact Submodule.zero_mem _
    · exact bot_le

/-- Exact FINITE-DIMENSIONAL rank defect for any real-linear physical
source S and detector Phi with ker S <= ker Phi:
    finrank(S(ker Phi)) + rank(Phi) = rank(S).
The proof applies rank-nullity to the genuine restricted source map
S|_(ker Phi) and uses the explicit subtype identification of its kernel.
It does NOT postulate injectivity or any frame constant. -/
theorem p4Q2IM_abstract_physicalInvisible_finrank_defect
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) :
    Module.finrank ℝ ↥(Phi.ker.map S) +
      Module.finrank ℝ ↥Phi.range =
      Module.finrank ℝ ↥S.range := by
  let K : Submodule ℝ E := Phi.ker
  let SK : K →ₗ[ℝ] F := S.domRestrict K
  have hRange : SK.range = K.map S := by
    ext f
    constructor
    · intro hf
      obtain ⟨k, hk⟩ := (LinearMap.mem_range).mp hf
      exact (Submodule.mem_map).mpr ⟨(k : E), k.property, hk⟩
    · intro hf
      obtain ⟨a, ha, heq⟩ := (Submodule.mem_map).mp hf
      exact (LinearMap.mem_range).mpr ⟨⟨a, ha⟩, heq⟩
  have hKerImage : SK.ker.map K.subtype = S.ker := by
    ext a
    constructor
    · intro ha
      obtain ⟨k, hk, heq⟩ := (Submodule.mem_map).mp ha
      have hZero : SK k = 0 := (LinearMap.mem_ker).mp hk
      apply (LinearMap.mem_ker).mpr
      change S a = 0
      rw [← heq]
      exact hZero
    · intro ha
      refine (Submodule.mem_map).mpr ⟨⟨a, hLe ha⟩, ?_, rfl⟩
      exact (LinearMap.mem_ker).mpr ((LinearMap.mem_ker).mp ha)
  have hKerRank :
      Module.finrank ℝ ↥SK.ker = Module.finrank ℝ ↥S.ker := by
    have h := Submodule.finrank_map_subtype_eq K SK.ker
    rw [hKerImage] at h
    exact h.symm
  have hRestriction := LinearMap.finrank_range_add_finrank_ker SK
  rw [hRange, hKerRank] at hRestriction
  change Module.finrank ℝ ↥(Phi.ker.map S) +
      Module.finrank ℝ ↥S.ker =
      Module.finrank ℝ ↥Phi.ker at hRestriction
  have hSource := LinearMap.finrank_range_add_finrank_ker S
  have hDetector := LinearMap.finrank_range_add_finrank_ker Phi
  omega

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Detector" =>
  p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "SourceSpan" =>
  (p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).range
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The ACTUAL detector-visible part of the physical source span,
orthogonal to the TRUE invisible sources inside the physical Haar-L²
inner product. Note the intersection with range S: the orthogonal
complement in the entire infinite-dimensional physical Hilbert space
would be much too large. -/
noncomputable def p4Q2IM_actualRightVisiblePhysicalSourceSubmodule :
    Submodule ℝ Phys :=
  (Invisible)ᗮ ⊓ SourceSpan

local notation "Visible" =>
  p4Q2IM_actualRightVisiblePhysicalSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Every actual signed fine-right physical source is the orthogonal
sum of a true GI-invisible physical source and a detector-visible
physical source. No positivity is assumed on the invisible component. -/
theorem p4Q2IM_actualPhysicalSourceSpan_orthogonal_split :
    Invisible ⊔ Visible = SourceSpan ∧ Disjoint Invisible Visible := by
  have hLe : Invisible ≤ SourceSpan :=
    p4Q2IL_actualPhysicalInvisible_le_actualSourceRange
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  letI : FiniteDimensional ℝ ↥SourceSpan := inferInstance
  letI : FiniteDimensional ℝ ↥Invisible :=
    Submodule.finiteDimensional_of_le hLe
  letI : CompleteSpace ↥Invisible := FiniteDimensional.complete ℝ ↥Invisible
  letI : (Invisible).HasOrthogonalProjection := inferInstance
  constructor
  · change Invisible ⊔ (Invisibleᗮ ⊓ SourceSpan) = SourceSpan
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLe
  · have hOrth : Disjoint Invisible Invisibleᗮ :=
      (Submodule.isOrtho_orthogonal_right Invisible).disjoint
    exact hOrth.mono_right inf_le_left

/-- Detector invisibility vanishes exactly when the physical source
synthesis has no extra invisible directions beyond its own kernel. -/
theorem p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation :
    Invisible = ⊥ ↔ (PhysicalSource).ker = JointKernel := by
  have hLe :
      (PhysicalSource).ker ≤ (Detector).ker :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have h :=
    p4Q2IM_abstract_invisibleMap_bot_iff_kernel_eq
      PhysicalSource Detector hLe
  simpa only [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel,
    p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule] using h

/-- IM's exact dimension-counting identity for the ORIGINAL interacting
SU(2) Wilson model. The real dimension of physically invisible signed
fine-right sources is exactly the rank EXCESS of physical synthesis over
the full two-Wilson-posterior GI detector, for all finite r and all
nonnegative fine beta. This is a formula, not a claim that it is zero. -/
theorem p4Q2IM_actualPhysicalInvisible_finrank_defect :
    Module.finrank ℝ ↥Invisible +
      Module.finrank ℝ ↥(Detector).range =
      Module.finrank ℝ ↥SourceSpan := by
  have hLe :
      (PhysicalSource).ker ≤ (Detector).ker :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hRank :=
    p4Q2IM_abstract_physicalInvisible_finrank_defect
      PhysicalSource Detector hLe
  simpa only [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel,
    p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule] using hRank

/-- Exact genuine physical criterion: the invisible physical Hilbert
submodule is zero iff the rank of the original physical synthesis equals
the rank of the ORIGINAL two-interacting-posterior GI detector. This
does not assert that the rank equality actually holds. -/
theorem p4Q2IM_actualPhysicalInvisible_eq_bot_iff_originalGIRankEq :
    Invisible = ⊥ ↔
      Module.finrank ℝ ↥SourceSpan =
      Module.finrank ℝ ↥(Detector).range := by
  have hLe :
      (PhysicalSource).ker ≤ (Detector).ker :=
    p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hRank :=
    p4Q2HL_abstract_kernel_eq_iff_range_finrank_eq
      PhysicalSource Detector hLe
  rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] at hRank
  exact (p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r).trans hRank

/-- On an actual nonzero physical source in the orthogonal GI-visible
sector, ORIGINAL interacting-Wilson GL spatial mass is strictly
positive for every nonnegative fine coupling. -/
theorem p4Q2IM_actualVisibleSource_originalWilsonGLMass_pos
    (hFrozen : 0 < beta n)
    (f : Phys) (hf : f ∈ Visible) (hf0 : f ≠ 0) :
    0 < OriginalMass f (Finset.univ : Finset Link) := by
  have hNotInvisible : f ∉ Invisible := by
    intro hInv
    have hBot : Invisible ⊓ Invisibleᗮ = ⊥ :=
      (Submodule.isOrtho_orthogonal_right Invisible).disjoint.eq_bot
    have hMemBot : f ∈ (⊥ : Submodule ℝ Phys) := by
      rw [← hBot]
      exact ⟨hInv, hf.1⟩
    apply hf0
    simpa only [Submodule.mem_bot] using hMemBot
  exact p4Q2IL_actualPhysicalSource_GLMass_pos_of_not_invisible
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen f hf.2 hNotInvisible

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_abstract_invisibleMap_bot_iff_kernel_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_abstract_physicalInvisible_finrank_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalSourceSpan_orthogonal_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalInvisible_finrank_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalInvisible_eq_bot_iff_originalGIRankEq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualVisibleSource_originalWilsonGLMass_pos
