import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCoreToPhysicalJointL2
import Mathlib.Tactic

/-!
# P4-Q2-BS: original Wilson Haar-reference polarization descends on L² representatives

BR constructs the REAL linear map from bounded, strongly measurable concrete
Wilson joint observables to the SAME physical Wilson ground-state joint L².
It also proves Q(F) ≤ 12 ‖T F‖² and therefore Q(F)=0 when T F=0.

BQ constructed the actual symmetric real bilinear polarization B of this
literal mass-weighted ORIGINAL twelve-color Wilson Haar reference.

Here the bound |B(aF,G)| ≤ Q(aF)+Q(G), together with true real homogeneity
and Q(aF)=a² Q(F), proves B(F,G)=0 whenever T F=0. No hidden positivity
or division-by-zero issue is allowed: the proof uses a strictly positive
abs-value denominator when assuming the cross term is nonzero.

Consequently BOTH the bilinear pairing and its diagonal Q are independent
of the concrete representative: T F=T G implies B(F,K)=B(G,K),
B(K,F)=B(K,G) and Q(F)=Q(G).

This proves representative independence ON THE IMAGE of the bounded
original Wilson concrete core. It does not yet construct a continuous
extension of the literal Wilson reference to every physical joint L²
class, nor a reverse reference Poincare or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "Q" =>
  p4Q2BP_originalCoreReference H N hN beta hbeta
local notation "B" =>
  p4Q2BP_originalCorePolarization H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta

/-- A physical joint L²-null original Wilson concrete direction is in
the RADICAL of the genuine original mass-weighted Haar polarization.
The result is stronger than the already-proved Q-nullity in BR. -/
theorem p4Q2BS_originalPolarization_zero_left_of_physicalL2_zero
    (F G : Core) (hzero : T F = 0) :
    B F G = 0 := by
  have hQ : Q F = 0 :=
    p4Q2BR_originalCoreReference_eq_zero_of_physicalL2_zero
      H N hN beta hbeta F hzero
  have hQG : 0 ≤ Q G :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta G
  by_contra hne
  have hBpos : 0 < |B F G| := abs_pos.mpr hne
  let a : ℝ := (Q G + 1) / |B F G|
  have ha : 0 ≤ a :=
    div_nonneg (by linarith) hBpos.le
  have hBound :=
    p4Q2BQ_originalCorePolarization_abs_le
      H N hN beta hbeta (a • F) G
  rw [p4Q2BQ_originalCorePolarization_smul_left
      H N hN beta hbeta a F G,
    p4Q2BQ_originalCoreReference_smul
      H N hN beta hbeta a F,
    hQ] at hBound
  simp only [mul_zero, zero_add] at hBound
  have hCancel : |a * B F G| = Q G + 1 := by
    rw [abs_mul, abs_of_nonneg ha]
    change ((Q G + 1) / |B F G|) * |B F G| = Q G + 1
    exact div_mul_cancel₀ (Q G + 1) (ne_of_gt hBpos)
  rw [hCancel] at hBound
  linarith

/-- Nullity in the second variable follows from genuine BQ symmetry,
without any separate conditional-law approximation. -/
theorem p4Q2BS_originalPolarization_zero_right_of_physicalL2_zero
    (F G : Core) (hzero : T G = 0) :
    B F G = 0 := by
  calc
    B F G = B G F :=
      p4Q2BP_originalCorePolarization_symm H N hN beta hbeta F G
    _ = 0 :=
      p4Q2BS_originalPolarization_zero_left_of_physicalL2_zero
        H N hN beta hbeta G F hzero

/-- Genuine quotient representative independence in the FIRST variable:
two bounded original Wilson concrete observables representing the same
physical joint L² element have exactly the same Haar cross pairing. -/
theorem p4Q2BS_originalPolarization_congr_left
    (F G K : Core) (hEq : T F = T G) :
    B F K = B G K := by
  have hker : T (F - G) = 0 := by
    rw [map_sub, sub_eq_zero.mpr hEq]
  have hzero :=
    p4Q2BS_originalPolarization_zero_left_of_physicalL2_zero
      H N hN beta hbeta (F - G) K hker
  have hdecomp : F = (F - G) + G := by abel
  calc
    B F K = B ((F - G) + G) K :=
      congrArg (fun x : Core => B x K) hdecomp
    _ = B (F - G) K + B G K :=
      p4Q2BP_originalCorePolarization_add_left
        H N hN beta hbeta (F - G) G K
    _ = B G K := by rw [hzero, zero_add]

/-- Representative independence in the SECOND variable, from the same
symmetric original Wilson bilinear form. -/
theorem p4Q2BS_originalPolarization_congr_right
    (F G K : Core) (hEq : T F = T G) :
    B K F = B K G := by
  calc
    B K F = B F K :=
      p4Q2BP_originalCorePolarization_symm H N hN beta hbeta K F
    _ = B G K :=
      p4Q2BS_originalPolarization_congr_left H N hN beta hbeta F G K hEq
    _ = B K G :=
      p4Q2BP_originalCorePolarization_symm H N hN beta hbeta G K

/-- Invariance in BOTH slots, including when both concrete Wilson
representatives are independently changed within their physical L² class. -/
theorem p4Q2BS_originalPolarization_congr
    (F F' G G' : Core) (hF : T F = T F') (hG : T G = T G') :
    B F G = B F' G' := by
  calc
    B F G = B F' G :=
      p4Q2BS_originalPolarization_congr_left H N hN beta hbeta
        F F' G hF
    _ = B F' G' :=
      p4Q2BS_originalPolarization_congr_right H N hN beta hbeta
        G G' F' hG

/-- The ORIGINAL real Wilson Haar quadratic energy is an unambiguous
function of the physical joint L² representative ON THE BOUNDED CORE IMAGE.
This statement does not yet assert an extension to all joint L². -/
theorem p4Q2BS_originalCoreReference_congr_physicalL2
    (F G : Core) (hEq : T F = T G) :
    Q F = Q G := by
  calc
    Q F = B F F :=
      (p4Q2BO_originalWilsonRealPolarization_self
        H N hN beta hbeta F.1).symm
    _ = B G F :=
      p4Q2BS_originalPolarization_congr_left H N hN beta hbeta F G F hEq
    _ = B G G :=
      p4Q2BS_originalPolarization_congr_right H N hN beta hbeta F G G hEq
    _ = Q G :=
      p4Q2BO_originalWilsonRealPolarization_self H N hN beta hbeta G.1

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
