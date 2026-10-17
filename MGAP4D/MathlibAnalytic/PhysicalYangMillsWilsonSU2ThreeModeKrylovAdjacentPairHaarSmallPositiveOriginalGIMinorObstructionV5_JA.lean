import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSmallPositiveHaarRowNonconstancyV5_IZ
import Mathlib.Tactic

/-!
# P4-Q2-JA — positive-small-fine-beta physical rank and exact original GI obstruction

P4-Q2-IZ proves literal original Wilson Haar row nonconstancy at sufficiently
small strictly positive fine Wilson coupling, hence the ACTUAL physical
first fine-right Krylov source is linearly independent from the constant unit.

Use the genuinely interacting frozen-Wilson GI detector and the actual
physical Haar-L² source Gram from IU/IT. At positive frozen coupling and
sufficiently small strictly positive fine coupling:

* the real physical Gram quadratic of an HY-anchored depth-one pivot is > 0;
* the actual GI-invisible Hilbert sector is NONZERO precisely when EVERY
  genuine second physical Wilson two-posterior GI context minor vanishes;
* a positive original Wilson GL/source-norm lower bound for the whole
  two-dimensional physical source span exists precisely when SOME genuine
  Wilson GI two-context minor is nonzero.

The minor's nonzero existence is NOT proved here. The all-zero minor branch
is a real nonzero *physical* source invisible to the original GI detector,
not an algebraic dependent-coefficient artifact. There is no invented
independent-Haar posterior, no uniform H/n/spacing/depth lower bound, no
H1-C3 closure and no continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2JA_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRightDepthOne

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "Invisible" =>
  p4Q2IL_actualRightPhysicallyInvisibleSourceSubmodule
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "FineTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "PhysicalUnit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2

/-- For the actual original two-Wilson-posterior detector, noncollinearity of
the real fine Wilson Krylov source is PROVED in a small-positive-beta window.
The anchored pivot has strictly positive PHYSICAL Hilbert Gram. The exact
remaining obstruction is vanishing of ALL authentic Wilson GI two-context
minors: a nonzero GI-invisible Hilbert sector exists iff those minors vanish. -/
theorem p4Q2JA_smallFine_actualPivotGram_pos_and_invisible_iff_allWilsonMinors_zero
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ ε : ℝ, 0 < ε ∧
      (0 < beta (n + 1) → beta (n + 1) < ε →
        ∃ z : Pair,
          Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
          (0 < star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
            (Qsrc *ᵥ p4Q2IS_depthOnePivot (Modal e z))) ∧
          (Invisible ≠ ⊥ ↔
            ∀ e' : Link, ∀ z' : Pair,
              p4Q2IT_depthOneTwoContextMinor
                (Modal e z) (Modal e' z') = 0)) := by
  obtain ⟨ε, hε, hFineNonEigen⟩ :=
    p4Q2IZ_actualFineUnit_notEigenline_for_small_positive_beta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  refine ⟨ε, hε, ?_⟩
  intro hFinePos hFineSmall
  have hNE : ¬ ∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit :=
    hFineNonEigen hFinePos hFineSmall
  obtain ⟨z, hAnchor, hObstruction⟩ :=
    p4Q2IU_actualDepthOne_invisible_iff_fineUnit_nonEigen_and_noMinors
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hGram :
      0 < star (p4Q2IS_depthOnePivot (Modal e z)) ⬝ᵥ
        (Qsrc *ᵥ p4Q2IS_depthOnePivot (Modal e z)) :=
    (p4Q2IU_actualDepthOne_pivotGram_pos_iff_fineUnit_notEigenline
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z hAnchor).mpr hNE
  refine ⟨z, hAnchor, hGram, ?_⟩
  simpa only [hNE, true_and] using hObstruction

/-- The true all-source r=1 original interacting-Wilson GL/source-norm
lower-floor condition in the small-positive-fine-beta regime is EXACTLY
nonvanishing of at least one genuine original two-posterior GI 2-context
minor. The former physical-dependence alternative is eliminated using
the actual Wilson spatial plaquette and Haar beta-derivative theorems;
the detector nondegeneracy itself is not asserted. -/
theorem p4Q2JA_smallFine_globalOriginalGLFloor_iff_exists_nonzero_WilsonMinor
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ ε : ℝ, 0 < ε ∧
      (0 < beta (n + 1) → beta (n + 1) < ε →
        ∃ z : Pair,
          Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0 ∧
          ((∃ c : ℝ, 0 < c ∧
              ∀ f : ↥((PhysicalSource).range),
                c * ‖(f : Phys)‖ ^ 2 ≤
                  OriginalMass (f : Phys) (Finset.univ : Finset Link)) ↔
            ∃ e' : Link, ∃ z' : Pair,
              p4Q2IT_depthOneTwoContextMinor
                (Modal e z) (Modal e' z') ≠ 0)) := by
  obtain ⟨ε, hε, hFineNonEigen⟩ :=
    p4Q2IZ_actualFineUnit_notEigenline_for_small_positive_beta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  refine ⟨ε, hε, ?_⟩
  intro hFinePos hFineSmall
  have hNE : ¬ ∃ t : ℝ, FineTransfer PhysicalUnit = t • PhysicalUnit :=
    hFineNonEigen hFinePos hFineSmall
  obtain ⟨z, hAnchor, hFloor⟩ :=
    p4Q2IU_actualDepthOne_globalGLFloor_iff_fineUnitEigen_or_WilsonMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨z, hAnchor, ?_⟩
  constructor
  · intro hMass
    rcases hFloor.mp hMass with hEigen | hMinor
    · exact False.elim (hNE hEigen)
    · exact hMinor
  · intro hMinor
    exact hFloor.mpr (Or.inr hMinor)

end ActualRightDepthOne
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JA_smallFine_actualPivotGram_pos_and_invisible_iff_allWilsonMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JA_smallFine_globalOriginalGLFloor_iff_exists_nonzero_WilsonMinor
