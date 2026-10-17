import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVisiblePhysicalGIEquivalenceV5_IO
import Mathlib.Tactic

/-!
# P4-Q2-IP: true physical Wilson visible-sector GI detection stability

IO establishes an ACTUAL real-linear equivalence
  Visible = (S(K))ᗮ ∩ range S ≃ₗ range Phi,
where S is the genuine Haar-L² signed fine-right physical synthesis
and Phi is the ORIGINAL two-interacting-Wilson-posterior GI detector.

The present step proves a quantitatively stable representation on
THIS LITERAL PHYSICAL HILBERT SUBMODULE, not on arbitrary coefficient
coordinates. The restriction of IN's physically descended detector
  Psi : range S → original GI observations
to Visible is injective, and is anti-Lipschitz with a strictly positive
finite-model constant by pinned mathlib finite-dimensional theory.

The constant is not asserted uniform in volume, spacing, scale, n,
frozen beta, fine beta or Krylov depth. The original Wilson GL mass is
strictly positive for every nonzero visible physical source as in IM,
but no full-source positivity at positive fine beta and r>0 follows:
the true invisible sector S(K) may remain nonzero.

No independent-Haar conditional model, Dobrushin contraction, unknown
source-frame assumption, H1-C3 closure, OS Hamiltonian or continuum
Yang--Mills mass-gap claim is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IP_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Injectivity of the actual detector restricted to a physically
visible complement requires ONLY the exact kernel of the detector
and disjointness from that kernel; no coordinate independence or
new physical source-frame is assumed. -/
theorem p4Q2IP_abstract_detector_injective_on_visible
    {F G : Type*}
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (I V W : Submodule ℝ F)
    (psi : V →ₗ[ℝ] G)
    (hW : W ≤ V)
    (hKer : psi.ker = I.comap V.subtype)
    (hDisj : Disjoint I W) :
    Function.Injective (psi.comp (W.inclusion hW)) := by
  intro a b hab
  have hZero : psi (W.inclusion hW (a - b)) = 0 := by
    change (psi.comp (W.inclusion hW)) (a - b) = 0
    rw [map_sub, hab, sub_self]
  have hKerW : W.inclusion hW (a - b) ∈ psi.ker :=
    (LinearMap.mem_ker).mpr hZero
  rw [hKer] at hKerW
  have hInI : ((a - b : W) : F) ∈ I := hKerW
  have hInW : ((a - b : W) : F) ∈ W := (a - b).property
  have hBoth : ((a - b : W) : F) ∈ I ⊓ W := ⟨hInI, hInW⟩
  rw [hDisj.eq_bot] at hBoth
  have hZeroW : a - b = 0 := by
    apply Subtype.ext
    simpa only [Submodule.mem_bot] using hBoth
  exact sub_eq_zero.mp hZeroW

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

/-- Literal original interacting-Wilson GI detection restricted to
the true Haar-L² orthogonal visible PHYSICAL source space. -/
noncomputable def p4Q2IP_actualRightVisiblePhysicalGIDetector :
    ↥Visible →ₗ[ℝ] (Link → C(Pair, ℝ)) := by
  have hW : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  exact PhysGI.comp (Visible.inclusion hW)

local notation "VisibleGI" =>
  p4Q2IP_actualRightVisiblePhysicalGIDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- No nonzero physical Haar-L² source in the actual orthogonal
visible sector is annihilated by all ORIGINAL two-posterior GI
observations, regardless of fine coupling and Krylov depth. -/
theorem p4Q2IP_actualRightVisiblePhysicalGIDetector_injective :
    Function.Injective VisibleGI := by
  have hW : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  have hKer :=
    p4Q2IN_actualRightPhysicalInducedGIDetector_ker_eq_invisible
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hDisj :=
    (p4Q2IM_actualPhysicalSourceSpan_orthogonal_split
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).2
  exact p4Q2IP_abstract_detector_injective_on_visible
    Invisible (PhysicalSource).range Visible PhysGI hW hKer hDisj

/-- Genuine fixed-finite-model physical-source GI frame:
on the ACTUAL visible physical Haar-L² sector, the original
interacting-Wilson full-boundary detector has an anti-Lipschitz
inverse with a strictly positive REAL physical constant.

This is a theorem of finite-dimensionality and injectivity,
not a H/n/r/spacing-uniform frame hypothesis. -/
theorem p4Q2IP_actualRightVisiblePhysicalGI_antilipschitz :
    ∃ c : NNReal, 0 < c ∧
      AntilipschitzWith c (fun f : ↥Visible => VisibleGI f) := by
  have hW : Visible ≤ (PhysicalSource).range := by
    change Invisibleᗮ ⊓ (PhysicalSource).range ≤ (PhysicalSource).range
    exact inf_le_right
  letI : FiniteDimensional ℝ ↥((PhysicalSource).range) := inferInstance
  letI : FiniteDimensional ℝ ↥Visible :=
    Submodule.finiteDimensional_of_le hW
  have hInjective :=
    p4Q2IP_actualRightVisiblePhysicalGIDetector_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  exact (LinearMap.injective_iff_antilipschitz VisibleGI).mp hInjective

/-- Positivity of BOTH the norm of the authentic GI response and
the original Wilson GL spatial mass on each nonzero actual visible
physical source; does not claim either is uniform across models. -/
theorem p4Q2IP_actualRightVisible_originalGI_and_GLMass_pos
    (hFrozen : 0 < beta n)
    (f : ↥Visible) (hf : f ≠ 0) :
    0 < ‖VisibleGI f‖ ∧
      0 < OriginalMass (f : Phys) (Finset.univ : Finset Link) := by
  have hInjective :=
    p4Q2IP_actualRightVisiblePhysicalGIDetector_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hDetected : VisibleGI f ≠ 0 := by
    intro hZero
    have hEq : VisibleGI f = VisibleGI 0 := by
      simpa using hZero
    exact hf (hInjective hEq)
  have hPhysNonzero : (f : Phys) ≠ 0 := by
    intro hZero
    apply hf
    apply Subtype.ext
    exact hZero
  exact ⟨norm_pos_iff.mpr hDetected,
    p4Q2IM_actualVisibleSource_originalWilsonGLMass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (f : Phys) f.property hPhysNonzero⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IP_abstract_detector_injective_on_visible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IP_actualRightVisiblePhysicalGIDetector_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IP_actualRightVisiblePhysicalGI_antilipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IP_actualRightVisible_originalGI_and_GLMass_pos
