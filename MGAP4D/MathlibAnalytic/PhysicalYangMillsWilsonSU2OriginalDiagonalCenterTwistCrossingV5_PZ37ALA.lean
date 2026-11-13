import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterSourceOddV5_PZ37AHW2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH22ToH25StepwiseThresholdFrontierV5_PZ37AKZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALA — genuine diagonal spatial center twist of crossing kernel

The original even-torus central SU(2) cochain built in AHW and the
true original Wilson crossing kernel are retained WITHOUT substitution.
AHW2 proved that the exact same spatial center twist makes the ORIGINAL
centered physical source odd and W_H(TA)=2*p_H-W_H(A).

We now certify the *diagonal* action (A,B) -> (TA,TB): every
per-link relative holonomy a⁻¹*b is invariant under the SAME fixed
central sign on both endpoints, hence the full ORIGINAL crossing
product kernel remains pointwise invariant. The centered two-endpoint
spatial source sum changes sign; its square is unchanged. The original
spatial halfweight admits an exactly dual exponential formula.

This is a genuine original-model algebraic/geometric input for a
future Haar pair symmetrization and stronger physical norm floor.
It is NOT a numerical Haar mass or fixed-beta H22 no-witness proof;
one may NOT use it as an unproved pair-measure pushforward theorem.
No existing Lean/physics/pin/root/workflow is changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace ENNReal BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALA_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "s" => p4Q2PZ37AHW_originalCenterSign

/-- The SAME true center phase on two SU(2) endpoints cancels from
their original relative holonomy; no commuting arbitrary SU(2)
matrices is used, only the proved centrality of s. -/
theorem p4Q2PZ37ALA_originalRelativeHolonomy_diagonalCenter
    (a b : G) (c : ZMod 2) :
    (a * s c)⁻¹ * (b * s c) = a⁻¹ * b := by
  have hc : (s c)⁻¹ = s c :=
    p4Q2PZ37AHW_originalCenterSign_inv c
  have hComm : s c * (a⁻¹ * b) = (a⁻¹ * b) * s c :=
    p4Q2PZ37AHW_originalCenterSign_commutes c (a⁻¹ * b)
  have hSq : s c * s c = (1 : G) := by
    calc
      s c * s c = s c * (s c)⁻¹ := by rw [hc]
      _ = 1 := mul_inv_cancel _
  calc
    (a * s c)⁻¹ * (b * s c) =
        s c * (a⁻¹ * b) * s c := by
      rw [mul_inv_rev, hc]
      group
    _ = (a⁻¹ * b) * (s c * s c) := by rw [hComm]; group
    _ = a⁻¹ * b := by rw [hSq, mul_one]

/-- True original one-link Wilson relative kernel unchanged by a
simultaneous central translate on the same two endpoints. -/
theorem p4Q2PZ37ALA_originalOneLinkKernel_diagonalCenter
    (beta : ℝ) (a b : G) (c : ZMod 2) :
    specialUnitaryWilsonRelativeKernel 2 beta (a * s c) (b * s c) =
      specialUnitaryWilsonRelativeKernel 2 beta a b := by
  change
    Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2
      ((a * s c)⁻¹ * (b * s c))) =
    Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 (a⁻¹ * b))
  rw [p4Q2PZ37ALA_originalRelativeHolonomy_diagonalCenter a b c]

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "τ" => p4Q2PZ37AHW_originalCenterCochain H
local notation "T" => p4Q2PZ37AHW_originalCenterTwist H
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H

/-- ACTUAL all-link Wilson crossing product kernel, unchanged under
the same original AHW center twist at both boundaries. -/
theorem p4Q2PZ37ALA_originalCrossingKernel_diagonalCenter
    (beta : ℝ) (A B : Cfg) :
    KC beta (T A) (T B) = KC beta A B := by
  simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel,
    periodicHypercubicEvenSpatialSliceLinkList, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro e _he
  exact p4Q2PZ37ALA_originalOneLinkKernel_diagonalCenter
    beta (A e) (B e) (τ e)

/-- The genuine simultaneous pair-center twist reverses the
unchanged ORIGINAL sum of both centered source values. -/
theorem p4Q2PZ37ALA_originalPairSource_diagonalCenter_odd
    (A B : Cfg) :
    fCont (T A) + fCont (T B) = -(fCont A + fCont B) := by
  rw [p4Q2PZ37AHW2_originalSource_centerTwist_odd H A,
    p4Q2PZ37AHW2_originalSource_centerTwist_odd H B]
  ring

/-- Even two-source square is exactly invariant pointwise, a useful
original second-moment integrand for future pair-Haar descent. -/
theorem p4Q2PZ37ALA_originalPairSourceSquare_diagonalCenter_even
    (A B : Cfg) :
    (fCont (T A) + fCont (T B)) ^ 2 =
      (fCont A + fCont B) ^ 2 := by
  rw [p4Q2PZ37ALA_originalPairSource_diagonalCenter_odd H A B]
  ring

/-- Original spatial halfweight after the genuine center twist:
the exact mean action pH appears, no new spatial potential. -/
theorem p4Q2PZ37ALA_originalHalfweight_diagonalCenter_dual
    (beta : ℝ) (A : Cfg) :
    Real.exp (-(beta / 2) * W (T A)) =
      Real.exp (-(beta * pH)) * Real.exp ((beta / 2) * W A) := by
  rw [p4Q2PZ37AHW2_originalSpatialWilson_centerTwist_complement H A,
    ← Real.exp_add]
  congr 1
  ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalRelativeHolonomy_diagonalCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalOneLinkKernel_diagonalCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalCrossingKernel_diagonalCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalPairSource_diagonalCenter_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalPairSourceSquare_diagonalCenter_even
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALA_originalHalfweight_diagonalCenter_dual
