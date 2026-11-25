import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalTimeOneOSStrictPositivityV5_PZ37APN
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTwoModeOSGramKernelV5_PZ37ANG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APO — original finite-volume time-one OS two-mode positive definiteness

Candidate, not independently certified. Keep the original full-periodic
Wilson Gibbs form and ANF coefficients. APN covers every coefficient-one
direction; the missing pure constant direction is the actual positive
boundary vacuum. Use the original full-support Haar law to recover
pointwise constancy of the chosen continuous zeroth Gram--Schmidt mode.
This is not a volume-uniform bound or an OS/one-slab vacuum identification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "B" => PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "BM" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "OM" => periodicHypercubicEvenOpenHalfHaarMeasure
local notation "Gram" => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
local notation "M" => p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
local notation "Q" => p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
local notation "VacM" => periodicHypercubicEvenBoundaryVacuumMoment
local notation "Mode" => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode
local notation "F" => p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable

local instance p4Q2PZ37APO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APO_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37APO_haar : Measure.IsHaarMeasure (normalizedCompactHaar G) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The chosen continuous representative of the original Haar mode zero
is literally one. The upgrade from a.e. equality uses full-support Haar. -/
theorem p4Q2PZ37APO_originalContinuousModeZero_apply (U : G) :
    Mode 0 U = 1 := by
  let mu := normalizedCompactHaar G
  let f : SpecialUnitaryNormalizedHaarL2 2 :=
    ContinuousMap.toLp (E := ℝ) 2 mu ℝ (Mode 0)
  letI : Measure.IsHaarMeasure mu := by
    dsimp [mu]
    infer_instance
  have hRep : f =ᵐ[mu] Mode 0 :=
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := mu) (Mode 0)
  have hF : f = Lp.const 2 mu (1 : ℝ) :=
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp 0).trans
      p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne
  have hOne : (Lp.const 2 mu (1 : ℝ)) =ᵐ[mu] (fun _ => (1 : ℝ)) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := mu) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  have hfOne : f =ᵐ[mu] (fun _ => (1 : ℝ)) := by
    rw [hF]
    exact hOne
  have hEq : (fun U : G => Mode 0 U) =ᵐ[mu] (fun _ => (1 : ℝ)) :=
    hRep.symm.trans hfOne
  have hPoint : (fun U : G => Mode 0 U) = (fun _ => (1 : ℝ)) :=
    ((Mode 0).continuous.ae_eq_iff_eq mu continuous_const).1 hEq
  exact congrFun hPoint U

/-- The pure constant direction has exactly the original OS boundary vacuum
moment, times the same coefficient, with no transfer identification. -/
theorem p4Q2PZ37APO_originalTimeOneConstantBoundaryMoment
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 ≤ beta) (c : ℝ)
    (b : B H 2) :
    M H beta hb c 0 b = c * VacM H 2 (by norm_num) beta hb b := by
  unfold p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
    periodicHypercubicEvenBoundaryVacuumMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  change Gram H 2 (by norm_num) beta hb b x * F H c 0 (b,x) =
    c * Gram H 2 (by norm_num) beta hb b x
  have hObs : F H c 0 (b,x) = c := by
    simp [p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable,
      p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable,
      p4Q2PZ37ANA_timeOneTwoModeWilsonObservable,
      p4Q2PZ37APO_originalContinuousModeZero_apply]
  rw [hObs]
  exact mul_comm _ _

/-- Factor the nonzero second coefficient using the already certified
original boundary-moment linearity. -/
theorem p4Q2PZ37APO_originalTimeOneBoundaryMoment_ratio
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 ≤ beta)
    (c0 c1 : ℝ) (hc1 : c1 ≠ 0) (b : B H 2) :
    M H beta hb c0 c1 b = c1 * M H beta hb (c0 / c1) 1 b := by
  have h : c1 * (c0 / c1) = c0 := by
    calc
      c1 * (c0 / c1) = (c0 / c1) * c1 := mul_comm _ _
      _ = c0 := div_mul_cancel₀ c0 hc1
  calc
    _ = c0 * M H beta hb 1 0 b + c1 * M H beta hb 0 1 b :=
      p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear H beta hb c0 c1 b
    _ = c1 * ((c0 / c1) * M H beta hb 1 0 b + 1 * M H beta hb 0 1 b) := by
      rw [one_mul, mul_add, ← mul_assoc, h]
    _ = _ := congrArg (fun z : ℝ => c1 * z)
      (p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear
        H beta hb (c0 / c1) 1 b).symm

/-- The genuine OS form has no nonzero null coefficient pair at positive
coupling and every finite volume. No uniform lower bound is asserted. -/
theorem p4Q2PZ37APO_originalTimeOneOSQuadratic_pos_of_pair_ne_zero
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 < beta)
    (c0 c1 : ℝ) (hp : (c0,c1) ≠ (0,0)) :
    0 < Q H beta hb.le c0 c1 := by
  apply (p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_pos_iff_boundaryMoment_not_ae_zero
    H beta hb.le c0 c1).2
  intro hz
  by_cases h1 : c1 = 0
  · have h0 : c0 ≠ 0 := by
      intro h0
      exact hp (by simp [h0, h1])
    letI : IsProbabilityMeasure (BM H 2) := by
      dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
        FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
      infer_instance
    have hfalse : ∀ᵐ b ∂(BM H 2), False := by
      filter_upwards [hz] with b hzero
      change M H beta hb.le c0 c1 b = 0 at hzero
      rw [h1, p4Q2PZ37APO_originalTimeOneConstantBoundaryMoment] at hzero
      exact (mul_ne_zero h0 (ne_of_gt
        (periodicHypercubicEvenBoundaryVacuumMoment_pos H 2 (by norm_num) beta hb.le b))) hzero
    obtain ⟨_, hcontra⟩ := hfalse.exists
    exact hcontra
  · apply p4Q2PZ37APN_originalTimeOneBoundaryMoment_not_ae_zero H beta hb (c0 / c1)
    filter_upwards [hz] with b hzero
    change M H beta hb.le c0 c1 b = 0 at hzero
    rw [p4Q2PZ37APO_originalTimeOneBoundaryMoment_ratio H beta hb.le c0 c1 h1 b] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left h1

/-- Exact null coefficient classification at positive coupling. -/
theorem p4Q2PZ37APO_originalTimeOneOSQuadratic_zero_iff_pair_zero
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 < beta) (c0 c1 : ℝ) :
    Q H beta hb.le c0 c1 = 0 ↔ (c0,c1) = (0,0) := by
  constructor
  · intro hz
    by_contra hp
    exact (ne_of_gt (p4Q2PZ37APO_originalTimeOneOSQuadratic_pos_of_pair_ne_zero
      H beta hb c0 c1 hp)) hz
  · intro hp
    have h0 : c0 = 0 := congrArg Prod.fst hp
    have h1 : c1 = 0 := congrArg Prod.snd hp
    rw [h0, h1]
    apply p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_zero_of_modeCancellation
    filter_upwards with b
    simp

/-- The mode-one original boundary moment is not proportional to the actual
OS boundary vacuum moment. In particular genuine OS centering does not
annihilate it; the Gauss-law one-slab vacuum remains a separate carrier. -/
theorem p4Q2PZ37APO_originalTimeOneModeOne_not_vacuum_multiple
    (H : ℕ) [Nontrivial G] (beta : ℝ) (hb : 0 < beta) (r : ℝ) :
    ¬ (M H beta hb.le 0 1 =ᵐ[BM H 2]
      (fun b => r * VacM H 2 (by norm_num) beta hb.le b)) := by
  intro hz
  apply p4Q2PZ37APN_originalTimeOneBoundaryMoment_not_ae_zero H beta hb (-r)
  filter_upwards [hz] with b hzero
  change M H beta hb.le 0 1 b = r * VacM H 2 (by norm_num) beta hb.le b at hzero
  rw [p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear,
    p4Q2PZ37APO_originalTimeOneConstantBoundaryMoment, hzero]
  ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalContinuousModeZero_apply
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalTimeOneConstantBoundaryMoment
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalTimeOneBoundaryMoment_ratio
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalTimeOneOSQuadratic_pos_of_pair_ne_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalTimeOneOSQuadratic_zero_iff_pair_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APO_originalTimeOneModeOne_not_vacuum_multiple
