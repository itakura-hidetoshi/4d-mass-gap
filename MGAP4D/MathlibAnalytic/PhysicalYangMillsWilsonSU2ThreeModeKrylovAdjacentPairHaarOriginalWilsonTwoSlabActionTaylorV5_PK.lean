import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabLiteralKernelV5_PJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonUniformQuadraticRemainderV5_JF
import Mathlib.Tactic

/-!
# P4-Q2-PK — true Wilson two-slab action, Boltzmann and first-order obstruction

PJ identified the UNMODIFIED original raw two-slab Wilson physical
transfer with a literal double spatial-Haar kernel integral:
  G2(B) = ∫ A ∫ X K_t(A,B) K_t(X,A) dHaar(X) dHaar(A).

This module identifies the ACTUAL Euclidean Wilson action in the
product of TWO consecutive COMPLETE one-slab kernels. With W denoting
the original spatial plaquette Wilson action and C the original
time-like crossing plaquette action,

  S2(X,A,B) = W(X)/2 + W(A) + W(B)/2 + C(X,A) + C(A,B).

The intermediate configuration A contributes its FULL spatial action,
not a halfweight. This is the EXACT original two-slab Boltzmann action:
  K_t(A,B) K_t(X,A) = exp(-t * S2(X,A,B)).

Its genuine finite-volume bound 0 <= S2 <= 2 M_H supplies a uniform
quadratic Taylor remainder on the ORIGINAL kernel product, without
differentiating the Perron eigenvector or replacing the Wilson kernel.

For two distinct right boundaries B,C, the difference
S2(X,A,B)-S2(X,A,C) is literally S(A,B)-S(A,C), at EVERY intermediate
and left boundary. Haar integration preserves this cancellation:
the first-order boundary differences of the unnormalized two-slab
and one-slab Boltzmann profiles have the SAME action coefficient.

An abstract scalar identity also records why any two first-order
profiles differing only by a spatially constant term have zero
three-point determinant at quadratic order. This is NOT yet a
computed nonzero higher Taylor coefficient: the concrete Wilson
second-order contribution and an actual nonzero configuration triple
remain OPEN.

Original SU(2), Gauss-law physical Hilbert space, separate frozen/fine
couplings and the true Wilson halfweights are unchanged. No substitute
posterior or spectral measure, Dobrushin, rank assumption, sorry,
admit, new axiom, U0 or continuum Yang–Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PK_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalTwoSlabBoltzmann
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- Genuine original complete two-slab action. It contains BOTH
spatial boundary halfweights and the FULL intermediate spatial
Wilson plaquette action, with two actual temporal crossing actions. -/
noncomputable def p4Q2PK_originalTwoSlabWilsonAction
    (X A B : Cfg) : ℝ :=
  (1 / 2 : ℝ) * W X + W A + (1 / 2 : ℝ) * W B +
    Cross X A + Cross A B

/-- Original two-slab spatial Wilson action is the SUM of the two
original complete one-slab actions, with no modifications. -/
theorem p4Q2PK_originalTwoSlabAction_eq_oneSlabSum
    (X A B : Cfg) :
    p4Q2PK_originalTwoSlabWilsonAction H X A B =
      S X A + S A B := by
  unfold p4Q2PK_originalTwoSlabWilsonAction
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  ring

/-- At EVERY triple of spatial SU(2) configurations, the original
Wilson intermediate spatial action occurs with coefficient ONE. -/
theorem p4Q2PK_originalTwoSlab_intermediateSpatialAction_full
    (X A B : Cfg) :
    p4Q2PK_originalTwoSlabWilsonAction H X A B =
      (1 / 2 : ℝ) * W X + W A +
        (1 / 2 : ℝ) * W B + Cross X A + Cross A B := by
  rfl

/-- The product of the two ORIGINAL Wilson one-slab kernels is
exactly the Boltzmann factor of the genuine two-slab action. -/
theorem p4Q2PK_originalTwoSlabKernelProduct_eq_exp
    (t : ℝ) (X A B : Cfg) :
    K t A B * K t X A =
      Real.exp (-t *
        p4Q2PK_originalTwoSlabWilsonAction H X A B) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
        H 2 t A B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
        H 2 t X A,
      ← Real.exp_add]
  rw [p4Q2PK_originalTwoSlabAction_eq_oneSlabSum]
  congr 1
  ring

/-- The literal ORIGINAL physical double-Haar Wilson two-slab kernel
is exactly the exponential of the genuine total two-slab action. -/
theorem p4Q2PK_originalLiteralTwoSlab_eq_actionBoltzmann
    (t : ℝ) (B : Cfg) :
    p4Q2PJ_originalWilsonLiteralTwoSlabKernel H t B =
      ∫ A : Cfg, ∫ X : Cfg,
        Real.exp (-t *
          p4Q2PK_originalTwoSlabWilsonAction H X A B) ∂haar ∂haar := by
  unfold p4Q2PJ_originalWilsonLiteralTwoSlabKernel
  apply integral_congr_ae
  filter_upwards with A
  apply integral_congr_ae
  filter_upwards with X
  exact p4Q2PK_originalTwoSlabKernelProduct_eq_exp H t X A B

/-- Dependence on the rightmost configuration in the TWO-slab
action arises ONLY through its last genuine one-slab action. -/
theorem p4Q2PK_originalTwoSlabAction_rightBoundaryDifference
    (X A B C : Cfg) :
    p4Q2PK_originalTwoSlabWilsonAction H X A B -
      p4Q2PK_originalTwoSlabWilsonAction H X A C =
        S A B - S A C := by
  rw [p4Q2PK_originalTwoSlabAction_eq_oneSlabSum,
    p4Q2PK_originalTwoSlabAction_eq_oneSlabSum]
  ring

/-- The first-variation ACTION coefficient of the true two-slab
Wilson kernel has the same spatial-boundary difference as the
original one-slab coefficient, AFTER both actual Haar integrations.
This does not infer differentiability of the double integral. -/
theorem p4Q2PK_originalTwoSlab_firstOrderHaarBoundaryDifference
    (B C : Cfg) :
    (∫ A : Cfg, ∫ X : Cfg,
      (p4Q2PK_originalTwoSlabWilsonAction H X A B -
       p4Q2PK_originalTwoSlabWilsonAction H X A C) ∂haar ∂haar) =
      ∫ A : Cfg, (S A B - S A C) ∂haar := by
  apply integral_congr_ae
  filter_upwards with A
  calc
    (∫ X : Cfg,
      (p4Q2PK_originalTwoSlabWilsonAction H X A B -
       p4Q2PK_originalTwoSlabWilsonAction H X A C) ∂haar) =
        ∫ X : Cfg, (S A B - S A C) ∂haar := by
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PK_originalTwoSlabAction_rightBoundaryDifference H X A B C
    _ = S A B - S A C := by simp

/-- The unchanged finite-lattice global action budget bounds the
TWO-slab action by exactly twice the one-slab budget. -/
theorem p4Q2PK_originalTwoSlabAction_le_doubleBudget
    (X A B : Cfg) :
    0 ≤ p4Q2PK_originalTwoSlabWilsonAction H X A B ∧
      p4Q2PK_originalTwoSlabWilsonAction H X A B ≤ 2 * M := by
  have hXA₀ : 0 ≤ S X A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) X A
  have hAB₀ : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) A B
  have hXA : S X A ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) X A
  have hAB : S A B ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) A B
  rw [p4Q2PK_originalTwoSlabAction_eq_oneSlabSum]
  constructor <;> linarith

/-- A uniform TRUE two-slab exponential Taylor error controlled by
the original finite-volume physical Wilson action budget M_H.
No new coupling, surrogate slab action or spectral source occurs. -/
theorem p4Q2PK_originalTwoSlabKernelProduct_quadraticRemainder_le
    (t : ℝ) (hsmall : ‖t * (2 * M)‖ ≤ 1)
    (X A B : Cfg) :
    ‖K t A B * K t X A - 1 +
        t * p4Q2PK_originalTwoSlabWilsonAction H X A B‖ ≤
      (t * (2 * M)) ^ 2 := by
  let S2 := p4Q2PK_originalTwoSlabWilsonAction H X A B
  have hS2₀ : 0 ≤ S2 :=
    (p4Q2PK_originalTwoSlabAction_le_doubleBudget H X A B).1
  have hS2le : S2 ≤ 2 * M :=
    (p4Q2PK_originalTwoSlabAction_le_doubleBudget H X A B).2
  have hM : 0 ≤ 2 * M := by
    have h := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
    positivity
  have hNorm : ‖-t * S2‖ ≤ ‖t * (2 * M)‖ := by
    calc
      ‖-t * S2‖ = ‖t‖ * S2 := by
        simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hS2₀]
      _ ≤ ‖t‖ * (2 * M) :=
        mul_le_mul_of_nonneg_left hS2le (norm_nonneg t)
      _ = ‖t * (2 * M)‖ := by
        rw [norm_mul]
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hM]
  have hExp := Real.norm_exp_sub_one_sub_id_le (le_trans hNorm hsmall)
  have hKernel :
      K t A B * K t X A - 1 + t * S2 =
        Real.exp (-t * S2) - 1 - (-t * S2) := by
    rw [p4Q2PK_originalTwoSlabKernelProduct_eq_exp]
    ring
  rw [hKernel]
  calc
    ‖Real.exp (-t * S2) - 1 - (-t * S2)‖ ≤
        ‖-t * S2‖ ^ 2 := hExp
    _ ≤ ‖t * (2 * M)‖ ^ 2 := by gcongr
    _ = (t * (2 * M)) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]

/-- At fine coupling zero, the literal original double-Haar Wilson
two-slab transfer of the physical unit is EXACTLY one. -/
theorem p4Q2PK_originalLiteralTwoSlab_betaZero
    (B : Cfg) :
    p4Q2PJ_originalWilsonLiteralTwoSlabKernel H 0 B = 1 := by
  rw [p4Q2PK_originalLiteralTwoSlab_eq_actionBoltzmann]
  simp

/-- Consequently the TRUE literal original Wilson three-point
determinant vanishes at fine coupling zero; this does not assert
vanishing at positive fine coupling. -/
theorem p4Q2PK_originalLiteralThreeSpatialMinor_betaZero
    (A B C : Cfg) :
    p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H 0 A B C = 0 := by
  simp [p4Q2PJ_originalWilsonLiteralThreeSpatialMinor,
    p4Q2IW_originalWilsonHaarRow_beta_zero,
    p4Q2PK_originalLiteralTwoSlab_betaZero]

/-- Elementary algebraic cancellation of the quadratic-order
three-point determinant of two profiles sharing the SAME spatial
first variation (possibly differing by a constant c).
This is an abstract polynomial identity, not an assertion that the
actual Wilson functions equal these truncated profiles. -/
theorem p4Q2PK_firstOrderProfiles_threeSpatialMinor_zero
    (a : Cfg → ℝ) (c t : ℝ) (A B C : Cfg) :
    ((1 + t * a B) - (1 + t * a A)) *
        ((1 + t * (a C + c)) - (1 + t * (a A + c))) -
      ((1 + t * a C) - (1 + t * a A)) *
        ((1 + t * (a B + c)) - (1 + t * (a A + c))) = 0 := by
  ring

end OriginalTwoSlabBoltzmann

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabAction_eq_oneSlabSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlab_intermediateSpatialAction_full
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabKernelProduct_eq_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalLiteralTwoSlab_eq_actionBoltzmann
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabAction_rightBoundaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlab_firstOrderHaarBoundaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabAction_le_doubleBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalTwoSlabKernelProduct_quadraticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalLiteralTwoSlab_betaZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_originalLiteralThreeSpatialMinor_betaZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PK_firstOrderProfiles_threeSpatialMinor_zero
