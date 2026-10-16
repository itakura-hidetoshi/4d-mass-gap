import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSourceNormUnconditionalUpperV5_IK
import Mathlib.Tactic

/-!
# P4-Q2-IL: invisible physical Wilson sources as an ACTUAL Hilbert submodule

For arbitrary finite n,r, positive original frozen beta(n) and arbitrary
nonnegative fine beta(n+1), original interacting two-Wilson-posterior GI
has a real coefficient-space joint null kernel K. The physical source
synthesis S is a DISTINCT linear map into the true gauge-invariant
Haar-L² Hilbert submodule. The only unconditional inclusion is
ker(S) <= K. It is not legitimate to replace K by ker(S) for positive
fine coupling at higher Krylov depths.

IL transports the obstruction to its own physical Hilbert space:
  I_physical := S(K) <= physical Haar-L² source space.
It proves for EVERY ACTUAL signed physical Krylov source f in S.range:
  original GL mass(f) = 0  iff  f belongs to I_physical;
  f not in I_physical  implies  original GL mass(f) > 0;
  0 <= original GL mass(f) <= C*||f||² for an ACTUAL C>0,
with C independent of the coefficient REPRESENTATION of f.

The key fiber-exactness is a theorem rather than an assumption:
  a in K  iff  S(a) in S(K).
The backward direction uses the already verified genuine
ker(S) <= K; no arbitrary physical source is equated to zero.

These results precisely isolate the remaining physical invisibility
obstruction for positive fine beta and r>0, without declaring it zero.
No invented posterior, Dobrushin assumption, uniform source-frame,
OS continuum limit or Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IL_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The image of the TRUE original all-context two-Wilson-posterior GI
kernel under the original physical Haar-L² source synthesis is an
actual real submodule of the ACTUAL gauge-invariant physical Hilbert
space. It need not be zero at positive fine coupling and higher depth. -/
noncomputable def p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule :
    Submodule ℝ Phys :=
  JointKernel.map PhysicalSource

local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Physicalizing the GI joint kernel does not introduce any additional
coefficient ambiguity: S(a) belongs to S(K) IFF a itself belongs to K.
The nontrivial converse uses the proved true physical ker(S) <= K. -/
theorem p4Q2IL_originalGI_jointKernel_iff_actualPhysicalInvisible
    (a : Coeff) :
    a ∈ JointKernel ↔ PhysicalSource a ∈ Invisible := by
  change a ∈ JointKernel ↔
    PhysicalSource a ∈ JointKernel.map PhysicalSource
  constructor
  · intro ha
    exact (Submodule.mem_map).mpr ⟨a, ha, rfl⟩
  · intro hVisibleZero
    obtain ⟨b, hb, hab⟩ := (Submodule.mem_map).mp hVisibleZero
    have hZero : PhysicalSource (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hZeroActual :
        (∑ j : Fin (r + 1),
          (a - b) j •
            physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n (j : ℕ)) = 0 := hZero
    have hDiff : a - b ∈ JointKernel :=
      p4Q2HG_actualSource_zero_mem_GIJointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (a - b) hZeroActual
    have hA : (a - b) + b ∈ JointKernel :=
      JointKernel.add_mem hDiff hb
    simpa only [sub_add_cancel] using hA

/-- The true physical invisible sector is literally contained in
the finite span of actual right-Krylov physical sources. -/
theorem p4Q2IL_actualPhysicalInvisible_le_actualSourceRange :
    Invisible ≤ (PhysicalSource).range := by
  intro f hf
  change f ∈ JointKernel.map PhysicalSource at hf
  obtain ⟨a, _ha, heq⟩ := (Submodule.mem_map).mp hf
  exact (LinearMap.mem_range).mpr ⟨a, heq⟩

/-- No reference conditional or synthetic physical metric occurs:
the zero-set of the true two-interacting-Wilson-posterior GL
pair-Haar spatial mass on physical sources is EXACTLY S(K). -/
theorem p4Q2IL_actualRight_originalWilsonGLMass_zero_iff_physicalInvisible
    (hFrozen : 0 < beta n) (a : Coeff) :
    OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) = 0 ↔
      PhysicalSource a ∈ Invisible := by
  change
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ))
      (Finset.univ : Finset Link) = 0 ↔
    PhysicalSource a ∈ Invisible
  exact (p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a).trans
    (p4Q2IL_originalGI_jointKernel_iff_actualPhysicalInvisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a)

/-- This source-space statement is intrinsic: its truth does not depend
on choosing an arbitrary coefficient representation of the same
gauge-invariant physical Haar-L² input f. -/
theorem p4Q2IL_actualPhysicalSource_GLMass_zero_iff_invisible
    (hFrozen : 0 < beta n)
    (f : Phys) (hf : f ∈ (PhysicalSource).range) :
    OriginalMass f (Finset.univ : Finset Link) = 0 ↔
      f ∈ Invisible := by
  obtain ⟨a, rfl⟩ := (LinearMap.mem_range).mp hf
  exact p4Q2IL_actualRight_originalWilsonGLMass_zero_iff_physicalInvisible
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a

/-- Genuine physical sources outside the ORIGINAL GI-invisible
physical subspace have strictly positive original Wilson GL mass,
for arbitrary nonnegative fine coupling and finite Krylov depth. -/
theorem p4Q2IL_actualPhysicalSource_GLMass_pos_of_not_invisible
    (hFrozen : 0 < beta n)
    (f : Phys) (hf : f ∈ (PhysicalSource).range)
    (hVisible : f ∉ Invisible) :
    0 < OriginalMass f (Finset.univ : Finset Link) := by
  obtain ⟨a, rfl⟩ := (LinearMap.mem_range).mp hf
  have hNot : a ∉ JointKernel := by
    intro ha
    exact hVisible ((p4Q2IL_originalGI_jointKernel_iff_actualPhysicalInvisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mp ha)
  exact p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a hNot

/-- Unconditional finite-model UPPER source-norm bound IK and exact
physical invisible-zero-space classification are simultaneously valid
on the real finite-dimensional physical SOURCE SPAN, not merely for
a chosen list of coefficient coordinates. -/
theorem p4Q2IL_actualPhysicalSourceSpan_originalGL_upper_and_kernel
    (hFrozen : 0 < beta n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Phys), f ∈ (PhysicalSource).range →
        0 ≤ OriginalMass f (Finset.univ : Finset Link) ∧
        OriginalMass f (Finset.univ : Finset Link) ≤ C * ‖f‖ ^ 2 ∧
        (OriginalMass f (Finset.univ : Finset Link) = 0 ↔
          f ∈ Invisible) := by
  obtain ⟨C, hC, hBounds⟩ :=
    p4Q2IK_originalWilsonGLMass_global_nonneg_and_physicalSourceNorm_upper
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen
  refine ⟨C, hC, ?_⟩
  intro f hf
  obtain ⟨a, rfl⟩ := (LinearMap.mem_range).mp hf
  exact ⟨(hBounds a).1, (hBounds a).2,
    p4Q2IL_actualRight_originalWilsonGLMass_zero_iff_physicalInvisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_originalGI_jointKernel_iff_actualPhysicalInvisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_actualPhysicalInvisible_le_actualSourceRange
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_actualRight_originalWilsonGLMass_zero_iff_physicalInvisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_actualPhysicalSource_GLMass_zero_iff_invisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_actualPhysicalSource_GLMass_pos_of_not_invisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IL_actualPhysicalSourceSpan_originalGL_upper_and_kernel
