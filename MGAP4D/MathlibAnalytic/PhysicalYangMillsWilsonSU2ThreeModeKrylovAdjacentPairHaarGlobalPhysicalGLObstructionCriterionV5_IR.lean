import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVisiblePhysicalGLGramCoercivityV5_IQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLPhysicalSourceGlobalCoercivityCriterionV5_IJ
import Mathlib.Tactic

/-!
# P4-Q2-IR: exact physical Hilbert-space obstruction to global Wilson GL coercivity

IQ proves c ‖f‖² <= ORIGINAL interacting-Wilson GL spatial mass <= C ‖f‖²
for every ACTUAL Haar-L² source f in the TRUE orthogonal visible sector
  V_vis = (S(K))ᗮ ∩ range S
with model-dependent 0<c<=C. It does NOT assert S(K)=0 for positive
fine coupling and higher right-Krylov depth r.

IR closes the exact global obstruction criterion as a theorem on
ACTUAL PHYSICAL HAAR-L² sources, not merely on coefficient vectors:
  a strictly positive finite-model original GL/source-norm comparison
  on ALL f in range S
  IFF the genuine physically invisible submodule I_phys=S(K) is zero
  IFF the original GI detector and source synthesis ranks coincide.

The sufficient direction directly transports IQ's *visible* bound
to all sources under the (explicit and currently unproved at positive
fine beta, r>0) vanishing of I_phys. The necessary direction uses
the previously established genuine original Wilson IJ source floor
obstruction. None of these equivalent properties is asserted to hold
unconditionally in the positive-fine-coupling higher-depth regime.

No independent Haar posterior, Dobrushin, source frame assumption,
uniform-in-volume/spacing/depth lower bound, OS construction, or
continuum Yang--Mills mass-gap theorem is imported.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IR_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint
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
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Visible" =>
  p4Q2IM_actualRightVisiblePhysicalSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- Necessary AND sufficient REAL physical-Hilbert-space condition
for a positive ORIGINAL Wilson GL spatial mass coercivity floor plus
a genuine physical source-norm upper bound on ALL actual sources.
The right side quantifies over the literal physical source submodule
range S, not over artificial independent coefficient observables.

No claim that the left side holds for positive fine coupling r>0. -/
theorem p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_physicalNorm_comparison
    (hFrozen : 0 < beta n) :
    Invisible = ⊥ ↔
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ f : ↥((PhysicalSource).range),
          c * ‖(f : Phys)‖ ^ 2 ≤
            OriginalMass (f : Phys) (Finset.univ : Finset Link) ∧
          OriginalMass (f : Phys) (Finset.univ : Finset Link) ≤
            C * ‖(f : Phys)‖ ^ 2) := by
  constructor
  · intro hZero
    have hVisibleEq : Visible = (PhysicalSource).range := by
      have hSplit :=
        (p4Q2IM_actualPhysicalSourceSpan_orthogonal_split
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).1
      rw [hZero] at hSplit
      simpa using hSplit
    obtain ⟨c, C, hc, hcC, hVisibleComp⟩ :=
      p4Q2IQ_actualVisible_originalGL_physicalSourceNorm_comparison
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen
    refine ⟨c, C, hc, hcC, ?_⟩
    intro f
    have hfVisible : (f : Phys) ∈ Visible := by
      rw [hVisibleEq]
      exact f.property
    exact hVisibleComp ⟨(f : Phys), hfVisible⟩
  · rintro ⟨c, C, hc, hcC, hGlobal⟩
    apply (p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).mpr
    apply p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen c hc
    intro a
    exact (hGlobal ⟨PhysicalSource a,
      (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩).1

/-- A global positive original-Wilson mass lower bound on the TRUE
finite-dimensional physical Haar-L² source span exists if and only if
there is NO nonzero physically GI-invisible signed source. A
sufficient positive upper comparison always exists separately by IK. -/
theorem p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_lower
    (hFrozen : 0 < beta n) :
    Invisible = ⊥ ↔
      (∃ c : ℝ, 0 < c ∧
        ∀ f : ↥((PhysicalSource).range),
          c * ‖(f : Phys)‖ ^ 2 ≤
            OriginalMass (f : Phys) (Finset.univ : Finset Link)) := by
  constructor
  · intro hZero
    obtain ⟨c, C, hc, hcC, hGlobal⟩ :=
      (p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_physicalNorm_comparison
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen).mp hZero
    exact ⟨c, hc, fun f => (hGlobal f).1⟩
  · rintro ⟨c, hc, hLower⟩
    apply (p4Q2IM_actualPhysicalInvisible_eq_bot_iff_sourceSeparation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).mpr
    exact p4Q2IJ_originalWilson_global_sourceNorm_floor_implies_separation
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen c hc
      (fun a => hLower ⟨PhysicalSource a,
        (LinearMap.mem_range).mpr ⟨a, rfl⟩⟩)

/-- Equivalent fixed-model obstruction stated solely in terms of
ranks of the LITERAL two-original-Wilson-posterior GI detector and the
TRUE physical Haar-L² source synthesis. This is a RANK CRITERION,
not a proof that the missing equality of ranks actually holds. -/
theorem p4Q2IR_actualOriginalGIRank_eq_sourceRank_iff_global_originalGL_lower
    (hFrozen : 0 < beta n) :
    (Module.finrank ℝ ↥((PhysicalSource).range) =
       Module.finrank ℝ ↥((Detector).range)) ↔
      (∃ c : ℝ, 0 < c ∧
        ∀ f : ↥((PhysicalSource).range),
          c * ‖(f : Phys)‖ ^ 2 ≤
            OriginalMass (f : Phys) (Finset.univ : Finset Link)) := by
  exact (p4Q2IM_actualPhysicalInvisible_eq_bot_iff_originalGIRankEq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r).symm.trans
    (p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen)

/-- Contrapositive: a NONZERO physically GI-invisible source sector
is a strict obstruction to ANY positive global Wilson GL-mass floor
for the actual physical source norm. -/
theorem p4Q2IR_nonzeroInvisible_obstructs_all_global_originalGL_floors
    (hFrozen : 0 < beta n)
    (hInvisible : Invisible ≠ ⊥) :
    ¬ (∃ c : ℝ, 0 < c ∧
        ∀ f : ↥((PhysicalSource).range),
          c * ‖(f : Phys)‖ ^ 2 ≤
            OriginalMass (f : Phys) (Finset.univ : Finset Link)) := by
  intro hLower
  exact hInvisible
    ((p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).mpr hLower)

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_physicalNorm_comparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IR_actualInvisible_eq_bot_iff_global_originalGL_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IR_actualOriginalGIRank_eq_sourceRank_iff_global_originalGL_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IR_nonzeroInvisible_obstructs_all_global_originalGL_floors
