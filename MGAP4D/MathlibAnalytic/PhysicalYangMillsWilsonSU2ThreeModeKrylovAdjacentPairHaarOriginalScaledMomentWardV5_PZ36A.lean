import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStrippedQuarticHaarWardV5_PZ20
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# PZ36A — degree-four mixed Haar invariance under spatial-observable scaling

For the ORIGINAL finite-volume spatial SU(2) Haar, every mixed moment
integral w(X)^i Cross(X,B)^j with i+j <= 4 is independent of B.
Consequently integral (lambda*w(X)+Cross(X,B))^n is independent of B
for every real lambda and n <= 4. Lambda changes an auxiliary polynomial
observable, NOT the physical Wilson measure or posterior.

The lambda=2 case retains the FULL intermediate spatial weight in
Q(Y,X,B)-w(B) = L(Y,X)+2*w(X)+Cross(X,B).
No new axiom, sorry, admit, native_decide or replacement posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36A_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36A_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36A_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36A_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36A_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ36A_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36A_spatialProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section ScaledMomentWard
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
  (1 : G))

private theorem p4Q2PZ36A_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ36A_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

/-- Powers of the true spatial half-action are genuine gauge-invariant weights. -/
theorem p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant
    (i : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^i * Cross X B ∂haar) =
      (∫ X : Cfg, (w X)^i * Cross X I ∂haar) := by
  have hc : Continuous (fun X : Cfg => (w X)^i) :=
    (p4Q2PZ36A_half_continuous H).pow i
  have hInv : ∀ (g : Gauge) (X : Cfg),
      (w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 g X))^i = (w X)^i := by
    intro g X
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 g X]
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    H (fun X : Cfg => (w X)^i) hc hInv B

/-- Complete lower-degree mixed-moment invariance, on all even periods. -/
theorem p4Q2PZ36A_originalMixedMoment_invariant_le_four
    (i j : ℕ) (hij : i+j ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (w X)^i * (Cross X B)^j ∂haar) =
      (∫ X : Cfg, (w X)^i * (Cross X I)^j ∂haar) := by
  by_cases hi : i = 0
  · subst i
    simpa only [pow_zero,one_mul] using
      (p4Q2PZ19_originalFullCrossingPowerHaar_invariant H j B)
  by_cases hj : j = 0
  · subst j
    simp only [pow_zero,mul_one]
  by_cases hj1 : j = 1
  · subst j
    simpa only [pow_one] using
      (p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant H i B)
  by_cases hj2 : j = 2
  · subst j
    have hi12 : i = 1 ∨ i = 2 := by omega
    rcases hi12 with rfl | rfl
    · simpa only [pow_one] using
        (p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant H B)
    · exact p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant H B
  have hi1 : i = 1 := by omega
  have hj3 : j = 3 := by omega
  subst i
  subst j
  simpa only [pow_one] using
    (p4Q2PZ20_originalHalfSpatial_crossingCubeHaar_invariant H B)

/-- Mathlib's binomial formula through the original finite-volume Haar. -/
theorem p4Q2PZ36A_originalHaar_integral_binomial
    (f g : Cfg → ℝ) (hf : Continuous f) (hg : Continuous g) (n : ℕ) :
    (∫ X : Cfg, (f X+g X)^n ∂haar) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (∫ X : Cfg, (f X)^k * (g X)^(n-k) ∂haar) := by
  have hi (k : ℕ) :
      Integrable (fun X : Cfg => (n.choose k : ℝ) *
        ((f X)^k * (g X)^(n-k))) haar :=
    (continuous_const.mul ((hf.pow k).mul (hg.pow (n-k)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ X : Cfg, (f X+g X)^n ∂haar) =
        (∫ X : Cfg, ∑ k ∈ Finset.range (n+1),
          (n.choose k : ℝ)*((f X)^k*(g X)^(n-k)) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (∫ X : Cfg, (f X)^k*(g X)^(n-k) ∂haar) := by
      simpa only [integral_const_mul] using
        (integral_finset_sum (Finset.range (n+1)) (fun k _hk => hi k))

/-- Lambda=2 retains the double spatial weight at the true middle slice. -/
theorem p4Q2PZ36A_originalScaledStripMoment_invariant_le_four
    (lambda : ℝ) (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (lambda*w X+Cross X B)^n ∂haar) =
      (∫ X : Cfg, (lambda*w X+Cross X I)^n ∂haar) := by
  have hf : Continuous (fun X : Cfg => lambda*w X) :=
    continuous_const.mul (p4Q2PZ36A_half_continuous H)
  rw [p4Q2PZ36A_originalHaar_integral_binomial H
      (fun X : Cfg => lambda*w X) (fun X : Cfg => Cross X B)
      hf (p4Q2PZ36A_cross_continuous H B) n,
    p4Q2PZ36A_originalHaar_integral_binomial H
      (fun X : Cfg => lambda*w X) (fun X : Cfg => Cross X I)
      hf (p4Q2PZ36A_cross_continuous H I) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := by
    have hlt := Finset.mem_range.mp hk
    omega
  have hdeg : k+(n-k) ≤ 4 := by omega
  apply congrArg (fun t : ℝ => (n.choose k : ℝ)*t)
  calc
    (∫ X : Cfg, (lambda*w X)^k*(Cross X B)^(n-k) ∂haar) =
        lambda^k*(∫ X : Cfg, (w X)^k*(Cross X B)^(n-k) ∂haar) := by
      simp only [mul_pow,mul_assoc,integral_const_mul]
    _ = lambda^k*(∫ X : Cfg, (w X)^k*(Cross X I)^(n-k) ∂haar) := by
      rw [p4Q2PZ36A_originalMixedMoment_invariant_le_four H k (n-k) hdeg B]
    _ = (∫ X : Cfg, (lambda*w X)^k*(Cross X I)^(n-k) ∂haar) := by
      simp only [mul_pow,mul_assoc,integral_const_mul]

end ScaledMomentWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36A_originalMixedMoment_invariant_le_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36A_originalHaar_integral_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36A_originalScaledStripMoment_invariant_le_four
