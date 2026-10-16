import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarInvisibleOrthogonalRankV5_IM
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# P4-Q2-IN: exact ORIGINAL Wilson GI detector descent to physical Haar-L² sources

The actual physical source synthesis S and the full original two-INTERACTING-
Wilson-posterior GI detector Phi are real linear maps on the same finite
fine-right Krylov coefficient space. HJ proves ker S <= ker Phi (not equality).
Therefore the detector DESCENDS uniquely to the genuine physical source
span V=range S via the pinned mathlib first-isomorphism map
  E/ker(S) ≃ₗ V.
This is not a fictitious physical metric, projected one-posterior response,
or synthetic GI detector.

The physical GI detector Psi : V -> GI-observation-space obeys
  Psi(S(a)) = Phi(a),    range Psi = range Phi,
  ker Psi = { f in V : f in I_phys }.
At positive frozen beta and arbitrary nonnegative fine beta, the original
interacting-Wilson GL spatial mass vanishes precisely when Psi(f)=0.
Consequently the quotient of the ACTUAL physical source span by its
ACTUAL invisible part is linearly equivalent to the range of the actual
original interacting-Wilson GI detector.

The remaining assertion Psi injective on all V, equivalently I_phys=0,
at positive fine beta and r>0 is NOT supplied here. No uniform lower
bounds, independent conditional Haar posterior, Dobrushin, H1-C3,
OS reconstruction or continuum mass gap are inferred.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IN_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Universal source-to-detector descent. NO right inverse to S or extra
source-separation hypothesis is introduced. The only input is ker S <= ker Phi.
First quotient by ker S, then use the actual quotient-to-source-range
linear equivalence provided by pinned mathlib. -/
noncomputable def p4Q2IN_abstract_physicalInducedDetector
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) :
    S.range →ₗ[ℝ] G :=
  ((S.ker).liftQ Phi hLe).comp S.quotKerEquivRange.symm.toLinearMap

/-- The descended physical map evaluates exactly as the ORIGINAL detector,
regardless of the chosen signed Krylov coefficient representation. -/
theorem p4Q2IN_abstract_physicalInducedDetector_apply
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) (a : E) :
    p4Q2IN_abstract_physicalInducedDetector S Phi hLe
      ⟨S a, (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩ = Phi a := by
  change (S.ker).liftQ Phi hLe
    (S.quotKerEquivRange.symm
      ⟨S a, (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩) = Phi a
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- No original GI observation is lost, and none is invented, by descent
to the actual physical signed-source subspace. -/
theorem p4Q2IN_abstract_physicalInducedDetector_range_eq
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) :
    (p4Q2IN_abstract_physicalInducedDetector S Phi hLe).range =
      Phi.range := by
  ext y
  constructor
  · intro hy
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp hy
    obtain ⟨a, ha⟩ := (LinearMap.mem_range).mp f.property
    have hfa :
        f = ⟨S a, (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩ := by
      apply Subtype.ext
      exact ha.symm
    rw [hfa, p4Q2IN_abstract_physicalInducedDetector_apply] at hf
    exact (LinearMap.mem_range).mpr ⟨a, hf⟩
  · intro hy
    obtain ⟨a, ha⟩ := (LinearMap.mem_range).mp hy
    exact (LinearMap.mem_range).mpr
      ⟨⟨S a, (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩,
        (p4Q2IN_abstract_physicalInducedDetector_apply
          S Phi hLe a).trans ha⟩

/-- First isomorphism theorem for the PHYSICAL-source GI observable:
the quotient of range S by its genuine descended detector kernel is
isomorphic to the literal original GI detector range. This remains
valid if the detector has a nonzero invisible physical kernel. -/
noncomputable def p4Q2IN_abstract_physicalObservableQuotientEquiv
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (S : E →ₗ[ℝ] F) (Phi : E →ₗ[ℝ] G)
    (hLe : S.ker ≤ Phi.ker) :
    (S.range ⧸ (p4Q2IN_abstract_physicalInducedDetector S Phi hLe).ker)
      ≃ₗ[ℝ] Phi.range :=
  (p4Q2IN_abstract_physicalInducedDetector S Phi hLe).quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _
      (p4Q2IN_abstract_physicalInducedDetector_range_eq S Phi hLe))

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Pair" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
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
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The literal original two-interacting-Wilson-posterior GI detector
on the actual gauge-invariant physical Haar-L² source span. -/
noncomputable def p4Q2IN_actualRightPhysicalInducedGIDetector :
    (PhysicalSource).range →ₗ[ℝ] (Link → C(Pair, ℝ)) :=
  p4Q2IN_abstract_physicalInducedDetector PhysicalSource Detector
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)

local notation "PhysGI" =>
  p4Q2IN_actualRightPhysicalInducedGIDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Genuine physical-source descent equation: Psi(S(a))=Phi(a)
at ALL links and actual full SU(2) boundary contexts, with no
restriction on the nonnegative fine coupling or finite depth. -/
theorem p4Q2IN_actualRightPhysicalInducedGIDetector_apply
    (a : Coeff) :
    PhysGI ⟨PhysicalSource a,
      (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩ = Detector a := by
  exact p4Q2IN_abstract_physicalInducedDetector_apply
    PhysicalSource Detector
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a

/-- The range of the PHYSICAL induced Wilson GI map equals the range
of the original coefficient-space Wilson GI detector exactly. -/
theorem p4Q2IN_actualRightPhysicalInducedGIDetector_range_eq :
    (PhysGI).range = (Detector).range := by
  exact p4Q2IN_abstract_physicalInducedDetector_range_eq
    PhysicalSource Detector
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)

/-- The complete joint GI-invisible PHYSICAL Haar-L² sector is
precisely the kernel of the genuine descended physical GI detector,
as a submodule of range S. -/
theorem p4Q2IN_actualRightPhysicalInducedGIDetector_ker_eq_invisible :
    (PhysGI).ker = Invisible.comap (PhysicalSource).range.subtype := by
  ext f
  obtain ⟨a, ha⟩ := (LinearMap.mem_range).mp f.property
  have hf : f = ⟨PhysicalSource a,
      (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩ := by
    apply Subtype.ext
    exact ha.symm
  rw [hf]
  change PhysGI ⟨PhysicalSource a, _⟩ = 0 ↔
    PhysicalSource a ∈ Invisible
  rw [p4Q2IN_actualRightPhysicalInducedGIDetector_apply]
  have hK :=
    p4Q2IL_originalGI_jointKernel_iff_actualPhysicalInvisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  constructor
  · intro hZero
    have hKer : a ∈ (Detector).ker := (LinearMap.mem_ker).mpr hZero
    rw [p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] at hKer
    exact hK.mp hKer
  · intro hInvisible
    have haK : a ∈ JointKernel := hK.mpr hInvisible
    rw [← p4Q2HJ_actualRightGIContinuousDetector_ker_eq_jointKernel] at haK
    exact (LinearMap.mem_ker).mp haK

/-- Intrinsic original-Wilson physical GL zero-locus, expressed as
the literal physical GI detector kernel rather than a coefficient
kernel or an artificial independent-Haar conditional energy. -/
theorem p4Q2IN_actualRightOriginalGLMass_zero_iff_physicalDetector_zero
    (hFrozen : 0 < beta n)
    (f : (PhysicalSource).range) :
    OriginalMass (f : Phys) (Finset.univ : Finset Link) = 0 ↔
      PhysGI f = 0 := by
  have hIL :=
    p4Q2IL_actualPhysicalSource_GLMass_zero_iff_invisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (f : Phys) f.property
  have hKer :
      f ∈ (PhysGI).ker ↔ (f : Phys) ∈ Invisible := by
    rw [p4Q2IN_actualRightPhysicalInducedGIDetector_ker_eq_invisible]
    rfl
  exact hIL.trans (hKer.symm.trans (LinearMap.mem_ker))

/-- The actual physical Wilson source quotient, by precisely the
invisible physical sector, is linearly isomorphic to genuine all-context
Wilson GI observations. No claim that the invisible kernel is trivial. -/
noncomputable def p4Q2IN_actualRightPhysicalGIObservableQuotientEquiv :
    ((PhysicalSource).range ⧸ (PhysGI).ker)
      ≃ₗ[ℝ] (Detector).range :=
  p4Q2IN_abstract_physicalObservableQuotientEquiv PhysicalSource Detector
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_abstract_physicalInducedDetector_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_abstract_physicalInducedDetector_range_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_abstract_physicalObservableQuotientEquiv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_actualRightPhysicalInducedGIDetector_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_actualRightPhysicalInducedGIDetector_range_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_actualRightPhysicalInducedGIDetector_ker_eq_invisible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_actualRightOriginalGLMass_zero_iff_physicalDetector_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IN_actualRightPhysicalGIObservableQuotientEquiv
