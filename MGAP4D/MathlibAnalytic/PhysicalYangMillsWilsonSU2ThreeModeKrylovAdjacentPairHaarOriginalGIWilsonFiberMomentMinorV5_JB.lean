import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSmallPositiveOriginalGIMinorObstructionV5_JA
import Mathlib.Tactic

/-!
# P4-Q2-JB: ORIGINAL interacting-Wilson GI two-context minor as a physical fiber Haar determinant

JA proves that at sufficiently small strictly positive fine Wilson coupling
the true first two fine-right physical Krylov sources are noncollinear.
The open condition is the nonvanishing of an ORIGINAL two-interacting-Wilson
posterior GI detector 2-context minor, not an independent-Haar surrogate.

This file removes the coefficient-matrix packaging from that obstruction.
The exact original detector factors at each actual (link, left/right) context
as a strictly nonzero frozen-Wilson scalar times the ORIGINAL Haar fiber
integral of the true frozen transfer of each physical fine source against
the difference of the two interacting Wilson posterior densities.

Consequently the genuine GI 2-context minor is exactly the product of two
strictly nonzero physical frozen prefactors and a 2x2 determinant of four
literal true transfer/Haar/posterior-contrast integrals. This gives an exact
necessary and sufficient original Wilson INTEGRAL criterion for the positive
GL/source lower floor in JA's small-fine-beta region.

No actual nonzero moment determinant is asserted. No artificial source
frame, independently conditioned Haar posterior, Dobrushin, positive
volume/scale/depth-uniformity, H1-C3 or continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2JB_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The two actual coefficient selectors pick the two physical modes from
a real-linear modal functional. Kept separate to avoid large Wilson
configuration reductions in the finite-dimensional algebra. -/
private theorem p4Q2JB_abstract_modal_minor_eq_two_sample_det
    (w w' : Fin (1 + 1) → ℝ) :
    p4Q2IT_depthOneTwoContextMinor
      (p4Q2GY_modalTransferLinear 1 w)
      (p4Q2GY_modalTransferLinear 1 w') =
        w 0 * w' 1 - w 1 * w' 0 := by
  have h0 (v : Fin (1 + 1) → ℝ) :
      p4Q2GY_modalTransferLinear 1 v (p4Q2GX_rightZeroCoefficient 1) = v 0 :=
    p4Q2GY_modalTransferLinear_anchor 1 v
  have h1 (v : Fin (1 + 1) → ℝ) :
      p4Q2GY_modalTransferLinear 1 v p4Q2IS_depthOneCoefficient = v 1 := by
    simp [p4Q2GY_modalTransferLinear_apply, p4Q2IS_depthOneCoefficient]
  unfold p4Q2IT_depthOneTwoContextMinor
  rw [h0 w, h0 w', h1 w, h1 w']

section ActualWilsonFiberMinor

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
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 1
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The LITERAL original finite SU(2) normalized Haar fiber integral of
the genuine frozen transfer of the genuine fine-right physical Krylov
source at depth j=0,1, weighted by the difference of the two ORIGINAL
interacting Wilson conditional posterior densities. -/
noncomputable def p4Q2JB_originalWilsonTrueFiberMoment
    (e : Link) (z : Pair) (j : Fin (1 + 1)) : ℝ :=
  p4Q2GN_originalTransferFiberContrastMoment Hn (beta n) (hbeta n)
    (RightFactor n (j : ℕ)) e z

/-- The exact frozen original-Wilson scalar that multiplies each true Haar
moment in GN's interacting GI detector. It depends on the real physical
Wilson transfer norm and actual joint half-density, NOT a synthetic law. -/
noncomputable def p4Q2JB_originalWilsonFrozenPrefactor (z : Pair) : ℝ :=
  (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    Hn 2 (by norm_num) (beta n) (hbeta n)‖⁻¹) *
      continuousJointSqrtDensity Hn 2 (by norm_num) (beta n) (hbeta n) z

/-- This genuine Wilson prefactor is strictly nonzero for every finite
actual SU(2) pair boundary and every nonnegative frozen coupling. -/
theorem p4Q2JB_originalWilsonFrozenPrefactor_ne_zero (z : Pair) :
    p4Q2JB_originalWilsonFrozenPrefactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z ≠ 0 := by
  have hT :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        Hn 2 (by norm_num) (beta n) (hbeta n)‖ ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      Hn 2 (by norm_num) (beta n) (hbeta n)).ne'
  have hs :
      continuousJointSqrtDensity Hn 2 (by norm_num) (beta n) (hbeta n) z ≠ 0 :=
    (continuousJointSqrtDensity_pos Hn 2 (by norm_num) (beta n) (hbeta n) z).ne'
  unfold p4Q2JB_originalWilsonFrozenPrefactor
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hT)) hs

/-- Each modal coefficient of the ACTUAL ORIGINAL interacting Wilson GI
detector is the genuine frozen prefactor times a physical transfer/Haar
fiber moment; importantly, the two conditional laws have NOT been
replaced by independent Haar posteriors. -/
theorem p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
    (e : Link) (z : Pair) (j : Fin (1 + 1)) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z =
        p4Q2JB_originalWilsonFrozenPrefactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z *
        p4Q2JB_originalWilsonTrueFiberMoment
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z j := by
  simpa only [p4Q2JB_originalWilsonFrozenPrefactor,
    p4Q2JB_originalWilsonTrueFiberMoment] using
      (p4Q2GN_originalExpectationGap_eq_transferFiberMoment
        Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z)

/-- The actual physical Wilson moment 2x2 determinant at TWO physical
spatial links and TWO full genuine SU(2) left/right boundary contexts. -/
noncomputable def p4Q2JB_originalWilsonTrueFiberMomentMinor
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) : ℝ :=
  p4Q2JB_originalWilsonTrueFiberMoment
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z 0 *
    p4Q2JB_originalWilsonTrueFiberMoment
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z' 1 -
  p4Q2JB_originalWilsonTrueFiberMoment
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z 1 *
    p4Q2JB_originalWilsonTrueFiberMoment
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z' 0

/-- The genuine original interacting Wilson GI 2-context minor is
EXACTLY the product of two nonvanishing frozen-Wilson physical
prefactors and the determinant of four literal original fiber Haar
integrals. No positivity or rank hypothesis is slipped into this
identity. -/
theorem p4Q2JB_actualOriginalWilsonGIMinor_eq_trueFiberMomentMinor
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) :
    p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') =
      (p4Q2JB_originalWilsonFrozenPrefactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z *
      p4Q2JB_originalWilsonFrozenPrefactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z') *
      p4Q2JB_originalWilsonTrueFiberMomentMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z e' z' := by
  let P := p4Q2JB_originalWilsonFrozenPrefactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  let J := p4Q2JB_originalWilsonTrueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  change p4Q2IT_depthOneTwoContextMinor
      (p4Q2GY_modalTransferLinear 1
        (fun j : Fin (1 + 1) =>
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z))
      (p4Q2GY_modalTransferLinear 1
        (fun j : Fin (1 + 1) =>
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e' z')) =
      (P z * P z') * (J e z 0 * J e' z' 1 - J e z 1 * J e' z' 0)
  rw [p4Q2JB_abstract_modal_minor_eq_two_sample_det]
  have h0 := p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z 0
  have h1 := p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e z 1
  have h0' := p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z' 0
  have h1' := p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n e' z' 1
  change
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 1) e' z' -
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 1) e z *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e' z' =
      (P z * P z') * (J e z 0 * J e' z' 1 - J e z 1 * J e' z' 0)
  rw [h0, h1, h0', h1']
  ring

/-- At arbitrary fine coupling, nonvanishing of an actual original GI
2-context minor is EQUIVALENT to nonvanishing of the determinant of
four literal true interacting Wilson transfer-fiber Haar moments.
Both genuine frozen prefactors are nonzero, even for fine beta zero. -/
theorem p4Q2JB_actualOriginalWilsonGIMinor_ne_iff_trueFiberMomentMinor_ne
    (e : Link) (z : Pair) (e' : Link) (z' : Pair) :
    p4Q2IT_depthOneTwoContextMinor (Modal e z) (Modal e' z') ≠ 0 ↔
      p4Q2JB_originalWilsonTrueFiberMomentMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z e' z' ≠ 0 := by
  rw [p4Q2JB_actualOriginalWilsonGIMinor_eq_trueFiberMomentMinor]
  have hP := p4Q2JB_originalWilsonFrozenPrefactor_ne_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z
  have hP' := p4Q2JB_originalWilsonFrozenPrefactor_ne_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n z'
  constructor
  · intro h hZero
    exact h (by simp [hZero])
  · intro h
    exact mul_ne_zero (mul_ne_zero hP hP') h

/-- In the PROVED small-positive-fine-beta regime, a strictly positive
original interacting Wilson GL/source-norm lower bound for all genuine
physical depth-one Krylov sources is equivalent to nonzero determinant
of FOUR ACTUAL original-Wilson Haar fiber moments at two genuinely
physical link and left/right boundary contexts. This is a new explicit
integral (not coefficient rank) obstruction; its nonzero witness is
still open and no uniform coercivity is claimed. -/
theorem p4Q2JB_smallFine_globalOriginalGLFloor_iff_exists_trueFiberMomentMinor
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
              p4Q2JB_originalWilsonTrueFiberMomentMinor
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n e z e' z' ≠ 0)) := by
  obtain ⟨ε, hε, hCriterion⟩ :=
    p4Q2JA_smallFine_globalOriginalGLFloor_iff_exists_nonzero_WilsonMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨ε, hε, ?_⟩
  intro hpos hlt
  obtain ⟨z, hAnchor, hFloor⟩ := hCriterion hpos hlt
  refine ⟨z, hAnchor, ?_⟩
  exact hFloor.trans (exists_congr fun e' =>
    exists_congr fun z' =>
      p4Q2JB_actualOriginalWilsonGIMinor_ne_iff_trueFiberMomentMinor_ne
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e z e' z')

end ActualWilsonFiberMinor
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JB_originalWilsonFrozenPrefactor_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JB_actualWilsonModalResponse_eq_prefactor_mul_trueFiberMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JB_actualOriginalWilsonGIMinor_eq_trueFiberMomentMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JB_actualOriginalWilsonGIMinor_ne_iff_trueFiberMomentMinor_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JB_smallFine_globalOriginalGLFloor_iff_exists_trueFiberMomentMinor
