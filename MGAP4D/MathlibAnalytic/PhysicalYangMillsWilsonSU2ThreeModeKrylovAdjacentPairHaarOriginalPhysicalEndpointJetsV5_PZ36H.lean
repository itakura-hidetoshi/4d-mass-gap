import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalThirdMomentProfileV5_PZ36G
import Mathlib.Tactic

/-!
# P4-Q2-PZ36H — literal common-endpoint source moments in polynomial form

Six polynomial identities are obtained from PZ36D's original one- and
two-slab normalized SU(2) Haar integral endpoint-binomial proofs. No
artificial spectral data, posterior or extra assumptions are introduced.
The simultaneous two-slab input always uses the COMPLETE original Q.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36H_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36H_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36H_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36H_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36H_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36H_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36H_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalPhysicalEndpointJets
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H

theorem p4Q2PZ36H_originalOneFirst_endpoint (B : Cfg) :
    R1 1 B = w B + R1 1 I := by
  rw [p4Q2PZ36D_originalOneRaw_endpoint_binomial H 1 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalTwoFirst_endpoint (B : Cfg) :
    R2 1 B = w B + R2 1 I := by
  rw [p4Q2PZ36D_originalTwoRaw_endpoint_binomial H 1 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalOneSecond_endpoint (B : Cfg) :
    R1 2 B = (w B)^2 + 2*(R1 1 I)*(w B) + R1 2 I := by
  rw [p4Q2PZ36D_originalOneRaw_endpoint_binomial H 2 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalTwoSecond_endpoint (B : Cfg) :
    R2 2 B = (w B)^2 + 2*(R2 1 I)*(w B) + R2 2 I := by
  rw [p4Q2PZ36D_originalTwoRaw_endpoint_binomial H 2 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalOneThird_endpoint (B : Cfg) :
    R1 3 B = (w B)^3 + 3*(R1 1 I)*(w B)^2 +
      3*(R1 2 I)*(w B) + R1 3 I := by
  rw [p4Q2PZ36D_originalOneRaw_endpoint_binomial H 3 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalTwoThird_endpoint (B : Cfg) :
    R2 3 B = (w B)^3 + 3*(R2 1 I)*(w B)^2 +
      3*(R2 2 I)*(w B) + R2 3 I := by
  rw [p4Q2PZ36D_originalTwoRaw_endpoint_binomial H 3 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalOneFourth_endpoint (B : Cfg) :
    R1 4 B = (w B)^4 + 4*(R1 1 I)*(w B)^3 +
      6*(R1 2 I)*(w B)^2 + 4*(R1 3 I)*(w B) + R1 4 I := by
  rw [p4Q2PZ36D_originalOneRaw_endpoint_binomial H 4 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

theorem p4Q2PZ36H_originalTwoFourth_endpoint (B : Cfg) :
    R2 4 B = (w B)^4 + 4*(R2 1 I)*(w B)^3 +
      6*(R2 2 I)*(w B)^2 + 4*(R2 3 I)*(w B) + R2 4 I := by
  rw [p4Q2PZ36D_originalTwoRaw_endpoint_binomial H 4 (by omega) B]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

end OriginalPhysicalEndpointJets
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalOneFirst_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalTwoFirst_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalOneSecond_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalTwoSecond_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalOneThird_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalTwoThird_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalOneFourth_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36H_originalTwoFourth_endpoint
