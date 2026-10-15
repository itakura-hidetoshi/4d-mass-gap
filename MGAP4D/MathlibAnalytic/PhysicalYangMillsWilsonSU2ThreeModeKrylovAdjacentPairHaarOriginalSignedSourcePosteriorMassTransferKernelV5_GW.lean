import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundaryTransferNullCriterionV5_GU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundaryPhysicalContrastWilsonPosteriorMassV5_GU
import Mathlib.Tactic

/-!
# P4-Q2-GW: signed physical transfer nonzero detects genuine Wilson posterior squared mass

The first GU lane proves from the ORIGINAL SU(2) Wilson posterior
square-root minor that an actual signed physical source's ORIGINAL
Wilson transfer value t_f(B[e := Rpi]) != 0 forces a nonzero signed
two-LEFT-boundary FF receiver difference, and hence a positive Haar
REFERENCE squared difference mass, without requiring t_f > 0.

The independent second GU lane proves the squared difference of these
SAME two actual signed physical receiver rows under the ORIGINAL
interacting identity-left Wilson CONDITIONAL POSTERIOR dominates
exp(-16 beta) times its genuine Haar reference squared mass.

Combine both exact proofs for the SAME physical gauge-invariant Hilbert
source and SAME frozen Wilson beta to eliminate the positivity-of-source
restriction:

  t_f(B[e := Rpi]) != 0
    => true Wilson posterior integral |R_id-R_pi|^2 > 0.

Equivalently a zero original Wilson posterior squared two-response mass
forces t_f(B[e := Rpi])=0. Specialize the exact source-kernel obstruction
to actual fine right Krylov and left-three-mode signed source sums,
preserving fine beta(n+1) INSIDE the physical factors and frozen beta(n)
in the original transfer/receiver/conditional posterior.

This is a positive L² norm of a TWO-RESPONSE-ROW difference under one
genuine interacting posterior, NOT the distinct GI signed expectation
difference of ONE response under TWO posterior measures Delta. No claim
about GI detector injectivity, an all-coefficient source frame, spatial
summability, C1/C2/C3, H2/H3/H4 or the continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 730000

local instance p4Q2GW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- The ACTUAL original Wilson posterior squared physical two-boundary
receiver mass is strictly positive for any SIGNED original physical
source with nonzero Wilson transfer at the real pi insertion. No sign
condition on the source or its transfer integral is imposed. -/
theorem p4Q2GW_originalPhysicalPosteriorMass_pos_of_transfer_ne
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer :
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta hbeta f right e := by
  have hHaar : 0 <
      p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        H beta hbeta f right e :=
    p4Q2GU_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer_ne
      H beta hbeta hpos f right e hTransfer
  have hLower :=
    p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
      H beta hbeta f right e
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hHaar) hLower

/-- Zero squared mass under the TRUE original interacting Wilson
conditional posterior forces an EXACT obstruction: the actual
physical signed source's Wilson transfer vanishes at the pi right
insertion. No source-frame or injectivity hypothesis appears. -/
theorem p4Q2GW_originalPosteriorMass_zero_implies_transfer_zero
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hZero : p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta hbeta f right e = 0) :
    decomposableOneSliceTransferIntegral H 2 beta f
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  by_contra hNonzero
  have hPositive :=
    p4Q2GW_originalPhysicalPosteriorMass_pos_of_transfer_ne
      H beta hbeta hpos f right e hNonzero
  exact (ne_of_gt hPositive) hZero

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- TRUE adjacent fine-right Krylov signed coefficients remain inside
the physical source at fine beta(n+1), and the original frozen
beta(n) Wilson transfer nonzero condition forces strictly positive
genuine interacting Wilson posterior squared two-boundary response. -/
theorem p4Q2GW_actualRightKrylov_PosteriorMass_pos_of_transfer_ne
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (right : Cfg) (e : Link)
    (hTransfer :
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e := by
  have hT :
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)))
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0 := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hTransfer
  exact p4Q2GW_originalPhysicalPosteriorMass_pos_of_transfer_ne
    Hn (beta n) (hbeta n) hFrozen _ right e hT

/-- Necessary true Wilson source-kernel obstruction for ACTUAL
fine-right Krylov signed combinations, without replacing the source
by an abstract coefficient vector. -/
theorem p4Q2GW_actualRightKrylov_PosteriorMass_zero_implies_transfer_zero
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (right : Cfg) (e : Link)
    (hZero :
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        right e = 0) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  have h :=
    p4Q2GW_originalPosteriorMass_zero_implies_transfer_zero
      Hn (beta n) (hbeta n) hFrozen
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) right e hZero
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

/-- ACTUAL fine left-three-mode signed inputs inherit the same
posterior L² detectability criterion at frozen beta(n). -/
theorem p4Q2GW_actualLeftThreeMode_PosteriorMass_pos_of_transfer_ne
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (right : Cfg) (e : Link)
    (hTransfer :
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ k : Fin 3, a k • LeftFactor n r k)
      right e := by
  exact p4Q2GW_originalPhysicalPosteriorMass_pos_of_transfer_ne
    Hn (beta n) (hbeta n) hFrozen _ right e hTransfer

/-- Zero genuine Wilson posterior squared two-boundary response mass
forces zero frozen physical transfer of the SAME fine-evolved
left-three-mode signed physical source at the pi insertion. -/
theorem p4Q2GW_actualLeftThreeMode_PosteriorMass_zero_implies_transfer_zero
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (right : Cfg) (e : Link)
    (hZero :
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        right e = 0) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ k : Fin 3, a k • LeftFactor n r k)
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  have h := p4Q2GW_originalPosteriorMass_zero_implies_transfer_zero
    Hn (beta n) (hbeta n) hFrozen
    (∑ k : Fin 3, a k • LeftFactor n r k) right e hZero
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_originalPhysicalPosteriorMass_pos_of_transfer_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_originalPosteriorMass_zero_implies_transfer_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_actualRightKrylov_PosteriorMass_pos_of_transfer_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_actualRightKrylov_PosteriorMass_zero_implies_transfer_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_actualLeftThreeMode_PosteriorMass_pos_of_transfer_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GW_actualLeftThreeMode_PosteriorMass_zero_implies_transfer_zero
