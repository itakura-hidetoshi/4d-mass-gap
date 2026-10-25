import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalEndpointJetsV5_PZ36H
import Mathlib.Tactic

/-!
# P4-Q2-PZ36I — original physical sixth Ward coefficient transport

Uses ONLY the genuine original one/two-slab SU(2) Wilson Haar moments
(PK, PP2, PX, PZ1, PZ36D) and previously proved Ward selection.
One-slab/two-slab second-moment Taylor differences use the authentic
mixed intermediate-slice coefficient d and P4-Q2-PM, not an independent
Haar tensor factor or replacement posterior.

PZ36B's universal cancellation is invoked ONLY after all three
PZ23 source beta coefficients and the genuine PX sixth fourth-jet
coefficient have been identified at the original finite volume.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36I_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36I_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36I_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36I_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36I_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36I_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36I_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section ActualSixthWardCancellation
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H

/-- Physical mean of the genuine signed one-slab first source, measured
relative to the actual identity-boundary double/one-slab moments. -/
theorem p4Q2PZ36I_originalFirstMean_eq_difference :
    (∫ X : Cfg, a X ∂haar) = -(R2 1 I - R1 1 I) := by
  calc
    (∫ X : Cfg, a X ∂haar) =
        (∫ X : Cfg, -(R1 1 X) ∂haar) := by
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ36E_originalFirstAction_eq_negRaw H X
    _ = -(∫ X : Cfg, R1 1 X ∂haar) := by
      rw [integral_neg]
    _ = -(R2 1 I - R1 1 I) := by
      rw [p4Q2PZ36E_originalTwoFirst_identity_split H]
      ring

/-- No missing middle plaquettes: P4-Q2-PM's genuine mixed d slope
is the first two-slab minus one-slab Haar identity moment. -/
theorem p4Q2PZ36I_originalMixedSecond_difference
    (A B : Cfg) :
    d B - d A = (R2 1 I - R1 1 I)*(w B - w A) := by
  calc
    d B - d A =
        (∫ X : Cfg, a X ∂haar)*(a B-a A) :=
          p4Q2PM_originalMixedMoment_difference_proportional H A B
    _ = (R2 1 I - R1 1 I)*(w B-w A) := by
      rw [p4Q2PZ36I_originalFirstMean_eq_difference H,
        p4Q2PZ24_originalFirstTaylorAction_spatialDifference H A B]
      ring

/-- True second Taylor row b+2d differs by exactly the SAME boundary
polynomial as the complete original two-slab second raw Haar moment.
Only a boundary-independent constant can differ; none is postulated. -/
theorem p4Q2PZ36I_originalTwoSecondTaylorRow_difference
    (A B : Cfg) :
    (b B-b A)+2*(d B-d A) =
      PZ36EndpointAlgebra.second (R2 1 I) (R2 2 I) (w B) -
        PZ36EndpointAlgebra.second (R2 1 I) (R2 2 I) (w A) := by
  rw [p4Q2PZ36E_originalSecondAction_eq_raw H B,
    p4Q2PZ36E_originalSecondAction_eq_raw H A,
    p4Q2PZ36H_originalOneSecond_endpoint H B,
    p4Q2PZ36H_originalOneSecond_endpoint H A,
    p4Q2PZ36I_originalMixedSecond_difference H A B]
  unfold PZ36EndpointAlgebra.second
  ring

theorem p4Q2PZ36I_originalOneSecond_eq_endpoint (B : Cfg) :
    b B = PZ36EndpointAlgebra.second (R1 1 I) (R1 2 I) (w B) := by
  rw [p4Q2PZ36E_originalSecondAction_eq_raw H B,
    p4Q2PZ36H_originalOneSecond_endpoint H B]
  unfold PZ36EndpointAlgebra.second
  ring

theorem p4Q2PZ36I_originalOneThird_eq_endpoint (B : Cfg) :
    c B = PZ36EndpointAlgebra.third (R1 1 I) (R1 2 I) (R1 3 I) (w B) := by
  rw [p4Q2PZ36E_originalOneThird_eq_negRaw H B,
    p4Q2PZ36H_originalOneThird_endpoint H B]
  unfold PZ36EndpointAlgebra.third
  ring

theorem p4Q2PZ36I_originalTwoThird_eq_endpoint (B : Cfg) :
    g B = PZ36EndpointAlgebra.third (R2 1 I) (R2 2 I) (R2 3 I) (w B) := by
  rw [p4Q2PZ36E_originalTwoThird_eq_negRaw H B,
    p4Q2PZ36H_originalTwoThird_endpoint H B]
  unfold PZ36EndpointAlgebra.third
  ring

theorem p4Q2PZ36I_originalOneFourth_eq_endpoint (B : Cfg) :
    u B = PZ36EndpointAlgebra.fourth (R1 1 I) (R1 2 I) (R1 3 I)
      (R1 4 I) (w B) := by
  rw [p4Q2PZ36E_originalOneFourth_eq_raw H B,
    p4Q2PZ36H_originalOneFourth_endpoint H B]
  unfold PZ36EndpointAlgebra.fourth
  ring

theorem p4Q2PZ36I_originalTwoFourth_eq_endpoint (B : Cfg) :
    v B = PZ36EndpointAlgebra.fourth (R2 1 I) (R2 2 I) (R2 3 I)
      (R2 4 I) (w B) := by
  rw [p4Q2PZ36E_originalTwoFourth_eq_raw H B,
    p4Q2PZ36H_originalTwoFourth_endpoint H B]
  unfold PZ36EndpointAlgebra.fourth
  ring

/-- Exact ORIGINAL PX sixth coefficient, with signed odd action
moments and its native mixed d retained, is the verified PZ36B
common-endpoint polynomial. No surrogate row is substituted. -/
theorem p4Q2PZ36I_originalSixthJet_eq_endpointPolynomial
    (A B C : Cfg) :
    p4Q2PX_originalSixthFourthJetCoefficient H A B C =
      PZ36EndpointAlgebra.sixthCoefficient
        (R1 1 I) (R1 2 I) (R1 3 I) (R1 4 I)
        (R2 1 I) (R2 2 I) (R2 3 I) (R2 4 I)
        (w A) (w B) (w C) := by
  unfold p4Q2PX_originalSixthFourthJetCoefficient
    p4Q2PP2_originalSixthJetCoefficient
    PZ36EndpointAlgebra.sixthCoefficient PZ36EndpointAlgebra.wedge
  rw [p4Q2PZ36I_originalTwoSecondTaylorRow_difference H A C,
    p4Q2PZ36I_originalTwoSecondTaylorRow_difference H A B]
  rw [p4Q2PZ36I_originalOneSecond_eq_endpoint H A,
    p4Q2PZ36I_originalOneSecond_eq_endpoint H B,
    p4Q2PZ36I_originalOneSecond_eq_endpoint H C,
    p4Q2PZ36I_originalOneThird_eq_endpoint H A,
    p4Q2PZ36I_originalOneThird_eq_endpoint H B,
    p4Q2PZ36I_originalOneThird_eq_endpoint H C,
    p4Q2PZ36I_originalTwoThird_eq_endpoint H A,
    p4Q2PZ36I_originalTwoThird_eq_endpoint H B,
    p4Q2PZ36I_originalTwoThird_eq_endpoint H C,
    p4Q2PZ36I_originalOneFourth_eq_endpoint H A,
    p4Q2PZ36I_originalOneFourth_eq_endpoint H B,
    p4Q2PZ36I_originalOneFourth_eq_endpoint H C,
    p4Q2PZ36I_originalTwoFourth_eq_endpoint H A,
    p4Q2PZ36I_originalTwoFourth_eq_endpoint H B,
    p4Q2PZ36I_originalTwoFourth_eq_endpoint H C]
  ring

/-- Authentic PZ23 beta2/3/4 integral equalities are proved in
PZ36E/F/G, and the true PX coefficient is identified just above.
Therefore the ORIGINAL finite-volume sixth low Ward baseline
cancels, with no new moment assumption or posterior. -/
theorem p4Q2PZ36I_originalSixthWardLowBaseline_zero
    (A B C : Cfg) :
    p4Q2PZ32_originalSixthWardLowBaseline H A B C = 0 := by
  unfold p4Q2PZ32_originalSixthWardLowBaseline
    p4Q2PZ24_originalLowWardSymmetricQuadratic
  rw [p4Q2PZ36I_originalSixthJet_eq_endpointPolynomial H A B C,
    p4Q2PZ36G_originalLowCoeffHaar2_eq_trueMomentDifference H,
    p4Q2PZ36F_originalLowCoeffHaar3_eq_trueMomentDifference H,
    p4Q2PZ36E_originalLowCoeffHaar4_eq_trueMomentDifference H]
  exact PZ36EndpointAlgebra.lowSector_cancel
    (R1 1 I) (R1 2 I) (R1 3 I) (R1 4 I)
    (R2 1 I) (R2 2 I) (R2 3 I) (R2 4 I)
    (w A) (w B) (w C)

/-- Main objective: the original physical sixth Ward obstruction is
identically ZERO for every original finite even spatial period,
including H=0, and every genuine SU(2) boundary triple. -/
theorem p4Q2PZ36I_originalSixthWard_unconditional_zero
    (A B C : Cfg) :
    p4Q2PZ8_originalSixthWardObstruction H A B C = 0 := by
  rw [p4Q2PZ35D9D_originalSixthWard_lowOnly_unconditional H A B C,
    p4Q2PZ36I_originalSixthWardLowBaseline_zero H A B C]

theorem p4Q2PZ36I_originalCorrectedSixthJet_unconditional_zero
    (A B C : Cfg) :
    p4Q2PZ1_originalSixthFifthJetCoefficient H A B C = 0 :=
  (p4Q2PZ8_sixthWard_zero_iff H A B C).mp
    (p4Q2PZ36I_originalSixthWard_unconditional_zero H A B C)

end ActualSixthWardCancellation
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalFirstMean_eq_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalMixedSecond_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalTwoSecondTaylorRow_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalOneSecond_eq_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalOneThird_eq_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalTwoThird_eq_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalOneFourth_eq_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalTwoFourth_eq_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalSixthJet_eq_endpointPolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalSixthWardLowBaseline_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalSixthWard_unconditional_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36I_originalCorrectedSixthJet_unconditional_zero
