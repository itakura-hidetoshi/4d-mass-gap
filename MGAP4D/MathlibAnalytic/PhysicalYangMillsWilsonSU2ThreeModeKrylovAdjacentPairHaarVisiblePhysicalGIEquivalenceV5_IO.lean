import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalGIDetectorDescentV5_IN
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# P4-Q2-IO: true Wilson GI image represented uniquely in orthogonal visible physical sources

IM constructs the actual orthogonal Haar-L² subspace
  Visible = Invisibleᗮ ⊓ range S,
where Invisible = S(K) is IL's original two-Wilson-posterior GI-invisible
physical source submodule. IN constructs the genuine induced two-posterior
GI detector Psi on the physical span V = range S, with
  ker Psi = Invisible (INSIDE V)
  range Psi = range Phi.

This file proves the substantive missing geometric bridge:
  Visible ≃ₗ[ℝ] range Phi
via the ACTUAL restricted Psi, not a chosen abstract coefficient section.

The proof works with dependent original fine-right modes and at ALL
nonnegative fine couplings. It does not assume ker S = K and does not
claim the invisible subspace vanishes. The linear equivalence is NOT
declared isometric; no uniform GL/source coercivity, summability,
strong-limit closure, OS Hamiltonian or continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IO_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- For any real modules, if a detector on a submodule V vanishes
EXACTLY on the internal submodule I, and the ambient source has a
disjoint complement W to I inside V, restriction to W gives a REAL
linear equivalence onto the detector image. No finite frame, no
arbitrary norm and no positive lower constant enter this argument. -/
noncomputable def p4Q2IO_abstract_complementDetectorEquivRange
    {F G : Type*}
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (I V W : Submodule ℝ F)
    (psi : V →ₗ[ℝ] G)
    (hI : I ≤ V) (hW : W ≤ V)
    (hKer : psi.ker = I.comap V.subtype)
    (hSup : I ⊔ W = V)
    (hDisj : Disjoint I W) :
    W ≃ₗ[ℝ] psi.range := by
  let L : W →ₗ[ℝ] psi.range :=
    psi.rangeRestrict.comp (W.inclusion hW)
  have hInjective : Function.Injective L := by
    intro a b hab
    have hZero : L (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hPsiZero : psi (W.inclusion hW (a - b)) = 0 := by
      exact congrArg (fun y : psi.range => (y : G)) hZero
    have hKerW : W.inclusion hW (a - b) ∈ psi.ker :=
      (LinearMap.mem_ker).mpr hPsiZero
    rw [hKer] at hKerW
    have hInI : ((a - b : W) : F) ∈ I := hKerW
    have hInW : ((a - b : W) : F) ∈ W := (a - b).property
    have hZeroF : ((a - b : W) : F) = 0 := by
      have hBoth : ((a - b : W) : F) ∈ I ⊓ W := ⟨hInI, hInW⟩
      rw [hDisj.eq_bot] at hBoth
      simpa only [Submodule.mem_bot] using hBoth
    have hZeroW : a - b = 0 := by
      apply Subtype.ext
      exact hZeroF
    exact sub_eq_zero.mp hZeroW
  have hSurjective : Function.Surjective L := by
    intro y
    obtain ⟨v, hv⟩ := (LinearMap.mem_range).mp y.property
    have hInSup : (v : F) ∈ I ⊔ W := by
      rw [hSup]
      exact v.property
    obtain ⟨i, w, hsum⟩ := (Submodule.mem_sup').mp hInSup
    have hiKer : (⟨(i : F), hI i.property⟩ : V) ∈ psi.ker := by
      rw [hKer]
      exact i.property
    have hiZero : psi ⟨(i : F), hI i.property⟩ = 0 :=
      (LinearMap.mem_ker).mp hiKer
    have hvDecomp :
        v = (⟨(i : F), hI i.property⟩ : V) + W.inclusion hW w := by
      apply Subtype.ext
      simpa using hsum.symm
    have hPsiEq : psi v = psi (W.inclusion hW w) := by
      rw [hvDecomp, map_add, hiZero, zero_add]
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change psi (W.inclusion hW w) = (y : G)
    exact hPsiEq.symm.trans hv
  exact LinearEquiv.ofBijective L ⟨hInjective, hSurjective⟩

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
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Detector" =>
  p4Q2HJ_actualRightGIContinuousDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Visible" =>
  p4Q2IM_actualRightVisiblePhysicalSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "PhysGI" =>
  p4Q2IN_actualRightPhysicalInducedGIDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The actual original Wilson GI detector restricted to the
ORTHOGONAL VISIBLE PHYSICAL HAAR-L² source span is a real linear
equivalence onto the genuine full-boundary interacting-posterior
detector range. The domain is literally a submodule of physical
sources and the codomain is literally the original GI image. -/
noncomputable def p4Q2IO_actualRightVisiblePhysicalGIEquiv :
    ↥Visible ≃ₗ[ℝ] ↥((Detector).range) := by
  have hI : Invisible ≤ (PhysicalSource).range :=
    p4Q2IL_actualPhysicalInvisible_le_actualSourceRange
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hW : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  have hSplit :=
    p4Q2IM_actualPhysicalSourceSpan_orthogonal_split
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hKer :=
    p4Q2IN_actualRightPhysicalInducedGIDetector_ker_eq_invisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  let iso : ↥Visible ≃ₗ[ℝ] ↥((PhysGI).range) :=
    p4Q2IO_abstract_complementDetectorEquivRange
      Invisible (PhysicalSource).range Visible PhysGI
      hI hW hKer hSplit.1 hSplit.2
  exact iso.trans (LinearEquiv.ofEq _ _
    (p4Q2IN_actualRightPhysicalInducedGIDetector_range_eq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r))

/-- Geometric degree count: the visible physical Haar-L² dimension
equals the rank of the original two-Wilson-posterior GI detector,
without assuming the detector has the same rank as all sources. -/
theorem p4Q2IO_actualRightVisible_finrank_eq_originalGIRank :
    Module.finrank ℝ ↥Visible =
      Module.finrank ℝ ↥((Detector).range) := by
  exact (p4Q2IO_actualRightVisiblePhysicalGIEquiv
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r).finrank_eq

/-- The true physical Hilbert-orthogonal invisible/visible dimension
decomposition is the rank-nullity identity on physical sources,
NOT an assertion that the invisible rank vanishes. -/
theorem p4Q2IO_actualRightPhysicalInvisible_visible_finrank_add :
    Module.finrank ℝ ↥Invisible + Module.finrank ℝ ↥Visible =
      Module.finrank ℝ ↥((PhysicalSource).range) := by
  rw [p4Q2IO_actualRightVisible_finrank_eq_originalGIRank
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r]
  exact p4Q2IM_actualPhysicalInvisible_finrank_defect
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IO_abstract_complementDetectorEquivRange
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IO_actualRightVisiblePhysicalGIEquiv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IO_actualRightVisible_finrank_eq_originalGIRank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IO_actualRightPhysicalInvisible_visible_finrank_add
