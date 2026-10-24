import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCrossingSquareTraceOrthogonalityV5_PW
import Mathlib.Tactic

/-!
# P4-Q2-PW2 — true centered first Wilson profile is a plaquette trace sum

The ACTUAL original spatial Wilson action W(A) is a finite sum of
genuine plaquette energies E(U_p(A))=1-χ_p(A). The true Haar mean of
every χ_p is zero by PW's physical one-link SU(2) center-flip theorem.
Consequently the full original spatial Wilson Haar mean is the exact
finite plaquette count, and PM's actual first one-slab Haar moment
  a(A) = -W(A)/2 - c_H
has original Haar mean -card(plaquettes)/2 - c_H.

Thus the genuine centered physical first action profile appearing
in the PT3 two-crossing obstruction is, unconditionally,
  h(A) = a(A)-mean_H(a) = (1/2) * Σ_p χ_p(A).

No artificial Haar independence or redefinition of either posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PW2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PW2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PW2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PW2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PW2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PW2_nativeFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
namespace GroundStatePosteriorJoint

section OriginalWilsonCenteredPlaquetteSum
variable (H : ℕ)
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "cH" => p4Q2JE_originalWilsonHaarZeroDerivativeConstant H

/-- Exact sum of all ORIGINAL spatial plaquette real Wilson traces. -/
noncomputable def p4Q2PW2_originalAllPlaquetteRealTrace (A : Cfg) : ℝ :=
  ∑ p : Plaq, χ p A

local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H

theorem p4Q2PW2_originalAllPlaquetteRealTrace_continuous :
    Continuous (fun A : Cfg => Φ A) := by
  classical
  unfold p4Q2PW2_originalAllPlaquetteRealTrace
  apply continuous_finset_sum
  intro p _hp
  exact p4Q2PV_originalPlaquetteRealCharacter_continuous H p

/-- The actual Wilson spatial action is exactly the plaquette count
minus the complete real plaquette trace sum on EVERY configuration. -/
theorem p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum
    (A : Cfg) :
    W A = (Fintype.card Plaq : ℝ) - Φ A := by
  classical
  have hFinite : W A = ∑ p : Plaq, E (Hol A p) := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
      periodicHypercubicEvenSpatialSlicePlaquetteList
    exact
      Finset.sum_map_toList
        (Finset.univ : Finset Plaq)
        (fun p : Plaq => E (Hol A p))
  rw [hFinite]
  have hEnergy (p : Plaq) :
      E (Hol A p) = 1 - χ p A := by
    unfold p4Q2PV_originalPlaquetteRealCharacter
    ring
  simp_rw [hEnergy]
  simp [p4Q2PW2_originalAllPlaquetteRealTrace, Finset.sum_sub_distrib]

/-- The exact full spatial Wilson character sum is Haar centered. -/
theorem p4Q2PW2_originalAllPlaquetteRealTrace_HaarMean_zero :
    (∫ A : Cfg, Φ A ∂haar) = 0 := by
  classical
  have hEach (p : Plaq) :
      Integrable (fun A : Cfg => χ p A) haar :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, Φ A ∂haar) =
      ∫ A : Cfg, ∑ p : Plaq, χ p A ∂haar := rfl
    _ = ∑ p : Plaq, (∫ A : Cfg, χ p A ∂haar) := by
      rw [integral_finset_sum _ (fun p _ => hEach p)]
    _ = 0 := by
      simp [p4Q2PW_originalPlaquetteChar_HaarMean_zero H]

/-- The original complete spatial Wilson action has exactly its
number of plaquettes as its reference-Haar mean at any finite volume. -/
theorem p4Q2PW2_originalSpatialWilsonAction_HaarMean_eq_card :
    (∫ A : Cfg, W A ∂haar) = (Fintype.card Plaq : ℝ) := by
  have hPhiInt : Integrable (fun A : Cfg => Φ A) haar :=
    (p4Q2PW2_originalAllPlaquetteRealTrace_continuous H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSub :
      (∫ A : Cfg, (Fintype.card Plaq : ℝ) - Φ A ∂haar) =
        (∫ _A : Cfg, (Fintype.card Plaq : ℝ) ∂haar) -
        (∫ A : Cfg, Φ A ∂haar) := by
    simpa only [Pi.sub_apply] using
      (integral_sub (integrable_const _) hPhiInt)
  calc
    (∫ A : Cfg, W A ∂haar) =
        ∫ A : Cfg, (Fintype.card Plaq : ℝ) - Φ A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H A
    _ = (∫ _A : Cfg, (Fintype.card Plaq : ℝ) ∂haar) -
          (∫ A : Cfg, Φ A ∂haar) := hSub
    _ = (Fintype.card Plaq : ℝ) := by
      rw [p4Q2PW2_originalAllPlaquetteRealTrace_HaarMean_zero H]
      simp

/-- PM's true one-slab Haar action profile has an EXPLICIT finite
spatial-plaquette-count Haar mean, with the actual Wilson halfweight. -/
theorem p4Q2PW2_originalFirstActionMoment_HaarMean_eq :
    (∫ A : Cfg, a A ∂haar) =
      -(1 / 2 : ℝ) * (Fintype.card Plaq : ℝ) - cH := by
  have hWInt : Integrable (fun A : Cfg => W A) haar :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSplit :
      (∫ A : Cfg, (-(1 / 2 : ℝ)) * W A - cH ∂haar) =
        (∫ A : Cfg, (-(1 / 2 : ℝ)) * W A ∂haar) -
        (∫ _A : Cfg, cH ∂haar) := by
    simpa only [Pi.sub_apply] using
      (integral_sub (hWInt.const_mul _) (integrable_const _))
  calc
    (∫ A : Cfg, a A ∂haar) =
        ∫ A : Cfg, (-(1 / 2 : ℝ)) * W A - cH ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    _ = (∫ A : Cfg, (-(1 / 2 : ℝ)) * W A ∂haar) -
        (∫ _A : Cfg, cH ∂haar) := hSplit
    _ = (-(1 / 2 : ℝ)) * (∫ A : Cfg, W A ∂haar) - cH := by
      rw [integral_const_mul]
      simp
    _ = (-(1 / 2 : ℝ)) * (Fintype.card Plaq : ℝ) - cH := by
      rw [p4Q2PW2_originalSpatialWilsonAction_HaarMean_eq_card H]

/-- The TRUE Ward-centered original first-action profile equals exactly
one-half of the sum of real traces of ALL original spatial plaquettes. -/
theorem p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum (A : Cfg) :
    p4Q2PS_originalCenteredFirstMoment H A = (1 / 2 : ℝ) * Φ A := by
  unfold p4Q2PS_originalCenteredFirstMoment
    p4Q2PQ_originalFirstActionMean
  rw [p4Q2PM_originalFirstMoment_spatialWilson H A,
    p4Q2PW2_originalFirstActionMoment_HaarMean_eq H,
    p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H A]
  ring

end OriginalWilsonCenteredPlaquetteSum
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalAllPlaquetteRealTrace_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalAllPlaquetteRealTrace_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalSpatialWilsonAction_HaarMean_eq_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalFirstActionMoment_HaarMean_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum
