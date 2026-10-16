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
    exact (LinearMap.mem_ker).mpr ((Submodule.mem_bot).mp hMapped)
  · intro hEq
    apply le_antisymm
    · intro f hf
      obtain ⟨a, ha, heq⟩ := (Submodule.mem_map).mp hf
      have haSource : a ∈ S.ker := by rw [hEq]; exact ha
      have hZero : S a = 0 := (LinearMap.mem_ker).mp haSource
      rw [← heq, hZero]
      exact Submodule.zero_mem _
    · exact bot_le

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
local notation "SourceSpan" => (PhysicalSource).range
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
    exact hf0 ((Submodule.mem_bot).mp hMemBot)
  exact p4Q2IL_actualPhysicalSource_GLMass_pos_of_not_invisible
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen f hf.2 hNotInvisible

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_abstract_invisibleMap_bot_iff_kernel_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalSourceSpan_orthogonal_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualPhysicalInvisible_eq_bot_iff_originalGIRankEq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IM_actualVisibleSource_originalWilsonGLMass_pos
