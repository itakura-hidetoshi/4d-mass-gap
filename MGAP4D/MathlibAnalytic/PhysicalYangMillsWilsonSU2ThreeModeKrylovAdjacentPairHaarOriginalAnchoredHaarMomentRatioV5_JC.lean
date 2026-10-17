import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIWilsonFiberMomentMinorV5_JB
import Mathlib.Tactic

/-!
# P4-Q2-JC: real original Wilson GI anchor reduces a Haar minor to one signed fiber moment

JB proves the actual two-context interacting-Wilson GI minor is two
nonzero physical prefactors times a 2x2 determinant of four true
original transfer/Haar fiber moments.

This file specializes to a GENUINE original nonzero HY Wilson GI
zero-depth anchor. Its true zero-mode Haar moment J0(x) is nonzero:
therefore we may divide only by THIS concrete observed quantity.
The 2x2 physical Haar determinant equals J0(x) times the difference
between the true second-source Haar moment J1(y) and the anchored
multiple J1(x)/J0(x) of the true first-source moment J0(y).

The GL/source lower floor in the PROVED positive-small-fine window is
equivalent to one second original GI link/full SU(2) boundary context
whose explicitly normalized original Wilson Haar moment RESIDUAL
is nonzero. This still does NOT assert such a residual witness exists.
The interacting Wilson posteriors are never replaced by independent
Haar conditional laws; no continuum Yang-Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2JC_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Normalization of a genuine 2x2 determinant by one PROVED nonzero
pivot: no division by a possibly vanishing second-context value. -/
private theorem p4Q2JC_abstract_anchor_minor_eq_scaled_residual
    (a b c d : ℝ) (ha : a ≠ 0) :
    a * d - b * c = a * (d - (b / a) * c) := by
  field_simp [ha]
  ring

section ActualOriginalWilson

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
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "J" =>
  p4Q2JB_originalWilsonTrueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "P" =>
  p4Q2JB_originalWilsonFrozenPrefactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- A NONZERO true original GI zero-depth detector anchor automatically
implies that the actual original Wilson transfer/posterior-contrast
Haar fiber moment of the TRUE constant physical source is nonzero.
The frozen Wilson normalization is nonzero without any fine-beta
independence assumption. -/
theorem p4Q2JC_trueOriginalFiberMoment_zeroMode_ne_of_originalGI_anchor
    (e : Link) (z : Pair)
    (hAnchor : Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0) :
    J e z 0 ≠ 0 := by
  have h0 :
      Modal e z (p4Q2GX_rightZeroCoefficient 1) =
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n 0) e z := by
    change
      p4Q2GY_modalTransferLinear 1
        (fun j : Fin (1 + 1) =>
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z)
        (p4Q2GX_rightZeroCoefficient 1) = _
    rw [p4Q2GY_modalTransferLinear_anchor]
    rfl
  have hGI :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n 0) e z =
        P z * J e z 0 := by
    simpa only [Fin.val_zero] using
      (p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z 0)
  intro hZero
  apply hAnchor
  rw [h0, hGI, hZero, mul_zero]

/-- An explicit residual formed ONLY from the original Wilson
Haar moments at one real HY anchor x=(e,z) and one candidate second
physical context y=(e',z'). Divides by J0(x) only after its actual
GI detection has guaranteed that it is nonzero. -/
noncomputable def p4Q2JC_originalWilsonAnchoredSecondMomentResidual
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) : ℝ :=
  J e' z' 1 - (J e z 1 / J e z 0) * J e' z' 0

/-- The JB genuine physical Wilson Haar moment determinant is exactly
the anchored nonzero first moment times this single signed
second-context Haar moment residual. -/
theorem p4Q2JC_originalWilsonTrueMinor_eq_anchor_mul_secondResidual
    (e : Link) (z : Pair) (e' : Link) (z' : Pair)
    (hAnchor : Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0) :
    p4Q2JB_originalWilsonTrueFiberMomentMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z e' z' =
        J e z 0 *
          p4Q2JC_originalWilsonAnchoredSecondMomentResidual
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n e z e' z' := by
  have hJ : J e z 0 ≠ 0 :=
    p4Q2JC_trueOriginalFiberMoment_zeroMode_ne_of_originalGI_anchor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z hAnchor
  unfold p4Q2JB_originalWilsonTrueFiberMomentMinor
    p4Q2JC_originalWilsonAnchoredSecondMomentResidual
  exact p4Q2JC_abstract_anchor_minor_eq_scaled_residual
    (J e z 0) (J e z 1) (J e' z' 0) (J e' z' 1) hJ

/-- NONVANISHING of the original true physical two-context 2x2 Haar
moment minor is equivalent to ONE nonzero explicit genuine Wilson
Haar residual at the second actual physical link/full boundary.
No artificial rank or source frame. -/
theorem p4Q2JC_originalWilsonTrueMinor_ne_iff_secondResidual_ne
    (e : Link) (z : Pair) (e' : Link) (z' : Pair)
    (hAnchor : Modal e z (p4Q2GX_rightZeroCoefficient 1) ≠ 0) :
    p4Q2JB_originalWilsonTrueFiberMomentMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z e' z' ≠ 0 ↔
    p4Q2JC_originalWilsonAnchoredSecondMomentResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z e' z' ≠ 0 := by
  rw [p4Q2JC_originalWilsonTrueMinor_eq_anchor_mul_secondResidual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e z e' z' hAnchor]
  have hJ : J e z 0 ≠ 0 :=
    p4Q2JC_trueOriginalFiberMoment_zeroMode_ne_of_originalGI_anchor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e z hAnchor
  constructor
  · intro h hZero
    exact h (by rw [hZero, mul_zero])
  · intro hResidual
    exact mul_ne_zero hJ hResidual

/-- The new direct physical Wilson-Haar residual criterion for the
actual original interacting GL/source lower floor in the PROVED
small strictly positive fine-beta region at positive frozen coupling.
This does NOT assert that a residual witness is nonzero. -/
theorem p4Q2JC_smallFine_globalOriginalGLFloor_iff_exists_anchoredResidual
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
              p4Q2JC_originalWilsonAnchoredSecondMomentResidual
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n e z e' z' ≠ 0)) := by
  obtain ⟨ε, hε, hCriterion⟩ :=
    p4Q2JB_smallFine_globalOriginalGLFloor_iff_exists_trueFiberMomentMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨ε, hε, ?_⟩
  intro hFinePos hFineSmall
  obtain ⟨z, hAnchor, hFloor⟩ := hCriterion hFinePos hFineSmall
  refine ⟨z, hAnchor, ?_⟩
  exact hFloor.trans (exists_congr fun e' =>
    exists_congr fun z' =>
      p4Q2JC_originalWilsonTrueMinor_ne_iff_secondResidual_ne
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z e' z' hAnchor)

end ActualOriginalWilson
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JC_trueOriginalFiberMoment_zeroMode_ne_of_originalGI_anchor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JC_originalWilsonTrueMinor_eq_anchor_mul_secondResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JC_originalWilsonTrueMinor_ne_iff_secondResidual_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JC_smallFine_globalOriginalGLFloor_iff_exists_anchoredResidual
