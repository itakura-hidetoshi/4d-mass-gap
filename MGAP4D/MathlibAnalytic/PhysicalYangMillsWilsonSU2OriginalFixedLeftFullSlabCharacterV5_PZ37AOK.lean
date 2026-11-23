import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedLeftCrossingCharacterV5_PZ37AOJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOK — fixed-left original crossing and one-slab first Haar moments

For every finite periodic even H and every FIXED original left spatial-slice
configuration A, the original temporal crossing action has zero right-Haar
primary character insertion. This follows from AOJ's independently audited
single-link cancellation and the existing native finite-universe link sum.

Together with ANV's original exact primary Haar mean 0 and full spatial
Wilson action primary-character Haar pairing -1/4, the literal original
one-slab Wilson action has fixed-A conditional first Haar moment -1/8.
The new result does not postulate independent plaquettes, alter the original
Wilson/Haar/Gauss-law system, or construct a volume-uniform physical top slope.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOK_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- ANV's original primary spatial Wilson character is continuous on the
actual native spatial configuration, not on a synthetic plaquette product. -/
private theorem p4Q2PZ37AOK_primaryCharacter_continuous (H : ℕ) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
  have heq :
      (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) =
      (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
    funext B
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- The ORIGINAL full crossing action is a finite sum of terms already
shown by AOJ to have zero fixed-left right-Haar primary-character pairing.
This equality holds even for H=0, with no independent-link substitution. -/
theorem p4Q2PZ37AOK_originalCrossingAction_fixedLeft_primaryCharacter_haar_zero
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  have hChiCont : Continuous chi := p4Q2PZ37AOK_primaryCharacter_continuous H
  have hEachInt (e : Link) :
      Integrable (fun B : Cfg =>
        specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) * chi B) mu := by
    have hE : Continuous (fun B : Cfg =>
        specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e)) :=
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        (continuous_const.mul (continuous_apply e))
    exact (hE.mul hChiCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ B : Cfg,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B *
        chi B ∂mu) =
        ∫ B : Cfg, ∑ e : Link,
          specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) * chi B ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with B
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum
        H 2 A B, Finset.sum_mul]
    _ = ∑ e : Link,
        ∫ B : Cfg,
          specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) * chi B ∂mu := by
      exact MeasureTheory.integral_finset_sum
        (μ := mu) (s := (Finset.univ : Finset Link))
        (f := fun e B =>
          specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) * chi B)
        (by intro e _; exact hEachInt e)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      exact p4Q2PZ37AOJ_originalSingleCrossingEnergy_fixedLeft_primaryCharacter_zero H A e


private theorem p4Q2PZ37AOK_fixedLeftCrossing_continuous
    (H : ℕ) (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hPair : Continuous (fun B : Cfg => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg => B))
  change Continuous
    ((fun p : Cfg × Cfg => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 p.1 p.2) ∘
      (fun B : Cfg => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2).comp hPair

/-- The ORIGINAL complete one-slab action has exact first-character right-Haar
moment -1/8 with the left boundary held fixed. Unlike ANV's pair-Haar
moment this theorem claims no average over the left boundary. -/
theorem p4Q2PZ37AOK_originalOneSlabAction_fixedLeft_primaryCharacter_haar_eq_neg_eighth
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -(1 / 8 : ℝ) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let W := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
  let X := periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  have hChiCont : Continuous chi := p4Q2PZ37AOK_primaryCharacter_continuous H
  have hWCont : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hXCont : Continuous (fun B : Cfg => X A B) :=
    p4Q2PZ37AOK_fixedLeftCrossing_continuous H A
  have hChiInt : Integrable chi mu :=
    hChiCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWChiInt : Integrable (fun B : Cfg => W B * chi B) mu :=
    (hWCont.mul hChiCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hXChiInt : Integrable (fun B : Cfg => X A B * chi B) mu :=
    (hXCont.mul hChiCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZero : (∫ B : Cfg, chi B ∂mu) = 0 :=
    p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero H
  have hWMean : (∫ B : Cfg, W B * chi B ∂mu) = -(1 / 4 : ℝ) :=
    p4Q2PZ37ANV_originalFullSpatialAction_primaryCharacter_haarPairing H
  have hXZero : (∫ B : Cfg, X A B * chi B ∂mu) = 0 :=
    p4Q2PZ37AOK_originalCrossingAction_fixedLeft_primaryCharacter_haar_zero H A
  have hPoint (B : Cfg) :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B * chi B =
        ((1 / 2 : ℝ) * W A) * chi B +
          X A B * chi B + (1 / 2 : ℝ) * (W B * chi B) := by
    dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction, W, X]
    ring
  calc
    (∫ B : Cfg,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B *
        chi B ∂mu) =
      ∫ B : Cfg,
        ((1 / 2 : ℝ) * W A) * chi B +
          X A B * chi B + (1 / 2 : ℝ) * (W B * chi B) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with B
      exact hPoint B
    _ = ((1 / 2 : ℝ) * W A) * (∫ B : Cfg, chi B ∂mu) +
        (∫ B : Cfg, X A B * chi B ∂mu) +
        (1 / 2 : ℝ) * (∫ B : Cfg, W B * chi B ∂mu) := by
      calc
        _ = (∫ B : Cfg,
              ((1 / 2 : ℝ) * W A) * chi B + X A B * chi B ∂mu) +
              (∫ B : Cfg, (1 / 2 : ℝ) * (W B * chi B) ∂mu) :=
          integral_add ((hChiInt.const_mul _).add hXChiInt)
            (hWChiInt.const_mul _)
        _ = _ := by
          rw [integral_add (hChiInt.const_mul _) hXChiInt]
          rw [integral_const_mul, integral_const_mul]
    _ = -(1 / 8 : ℝ) := by
      rw [hZero, hXZero, hWMean]
      ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOK_originalCrossingAction_fixedLeft_primaryCharacter_haar_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOK_originalOneSlabAction_fixedLeft_primaryCharacter_haar_eq_neg_eighth
