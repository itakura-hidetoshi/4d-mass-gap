import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthHaarVandermondeSourceV5_PZ37D
import Mathlib.Tactic

/-!
# P4-Q2-PZ37E — original interacting TWO-slab stripped fifth Haar slope

The auxiliary doubled-spatial observable U5(2,B), already proved in PZ36
to have slope 15/16, is NOT by itself the actual original two-slab
Wilson action moment. This theorem transports that slope rigorously.

The literal original two-slab action Q(Y,X,B)=S(Y,X)+S(X,B)
contains the full intermediate spatial half-action TWICE. After stripping
only the rightmost w(B), the inner original normalized Haar integral
is expanded through degree five. Its lower four stripped moments
are genuinely boundary-invariant (PZ36A), while its fifth moment
is the actual PZ36 single-slab affine Haar result. The outer integral
then depends on B only through U5(2,B), so its genuine slope is 15/16.

No changed Wilson action, no independent factorization, no posterior
substitution, no new axiom/sorry/admit/native_decide. This alone does NOT
settle the sixth Haar obstruction or physical seventh coefficient.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37E_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37E_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37E_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37E_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37E_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37E_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37E_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section PhysicalTwoSlabFifthSlope
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
  (1 : G))
local notation "m" => p4Q2PZ36C_originalStripMoment H

/-- Genuine two-slab stripped fifth power of the FULL physical Wilson
action, with its original two Haar integrations and middle plaquettes. -/
noncomputable def p4Q2PZ37E_originalTwoStrippedFifth (B : Cfg) : ℝ :=
  ∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^5 ∂haar ∂haar

/-- Doubled-spatial source on the same original Haar, NOT a replacement
for the literal full two-slab action. -/
noncomputable def p4Q2PZ37E_originalDoubledStripMoment
    (n : ℕ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (2*w X+Cross X B)^n ∂haar

local notation "V" => p4Q2PZ37E_originalDoubledStripMoment H

/-- True inner Haar integration for the original Q, with all six
fifth-binomial sectors, not an independently factored posterior. -/
theorem p4Q2PZ37E_originalInnerTwoStrippedFifth
    (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B-w B)^5 ∂haar) =
      (2*w X+Cross X B)^5 +
      5*(m 1)*(2*w X+Cross X B)^4 +
      10*(m 2)*(2*w X+Cross X B)^3 +
      10*(m 3)*(2*w X+Cross X B)^2 +
      5*(m 4)*(2*w X+Cross X B) +
      m 5 + (15/32 : ℝ)*w X := by
  let t : ℝ := 2*w X+Cross X B
  have hc : Continuous (fun Y : Cfg => w Y+Cross Y X) :=
    (p4Q2PZ36C_half_continuous H).add
      (p4Q2PZ36C_cross_continuous H X)
  have hLow (k : ℕ) (hk : k ≤ 4) :
      (∫ Y : Cfg, (w Y+Cross Y X)^k ∂haar) = m k := by
    simpa only [one_mul, p4Q2PZ36C_originalStripMoment] using
      (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four
        H 1 k hk X)
  have hFifth :
      (∫ Y : Cfg, (w Y+Cross Y X)^5 ∂haar) =
        m 5 + (15/32 : ℝ)*w X := by
    simpa only [one_mul, p4Q2PZ36_originalScaledStrippedFifth,
      p4Q2PZ36C_originalStripMoment] using
      (p4Q2PZ36_originalScaledStrippedFifth_affine H 1 X)
  have hZero : m 0 = 1 := by
    simp [p4Q2PZ36C_originalStripMoment]
  calc
    (∫ Y : Cfg, (Q Y X B-w B)^5 ∂haar) =
      (∫ Y : Cfg, ((w Y+Cross Y X)+t)^5 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with Y
        rw [p4Q2PZ36C_originalTwoSlab_strip_eq H Y X B]
        rfl
    _ = ∑ k ∈ Finset.range 6, ((5 : ℕ).choose k : ℝ) *
        ((∫ Y : Cfg, (w Y+Cross Y X)^k ∂haar)*t^(5-k)) := by
      rw [p4Q2PZ36A_originalHaar_integral_binomial H
        (fun Y : Cfg => w Y+Cross Y X) (fun _ : Cfg => t)
        hc continuous_const 5]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [integral_mul_const]
    _ = (2*w X+Cross X B)^5 +
      5*(m 1)*(2*w X+Cross X B)^4 +
      10*(m 2)*(2*w X+Cross X B)^3 +
      10*(m 3)*(2*w X+Cross X B)^2 +
      5*(m 4)*(2*w X+Cross X B) +
      m 5 + (15/32 : ℝ)*w X := by
      dsimp [t]
      simp [Finset.sum_range_succ, Nat.choose, hZero,
        hLow 1 (by omega), hLow 2 (by omega),
        hLow 3 (by omega), hLow 4 (by omega), hFifth] <;> ring

/-- The original TWO-slab stripped fifth is an explicit original-Haar
outer polynomial. Lower powers of the r=2 observable are retained. -/
theorem p4Q2PZ37E_originalTwoStrippedFifth_outerExpansion
    (B : Cfg) :
    p4Q2PZ37E_originalTwoStrippedFifth H B =
      V 5 B + 5*(m 1)*V 4 B + 10*(m 2)*V 3 B +
      10*(m 3)*V 2 B + 5*(m 4)*V 1 B +
      m 5 + (15/32 : ℝ)*(∫ X : Cfg, w X ∂haar) := by
  let f : Fin 7 → Cfg → ℝ :=
    ![fun X => (2*w X+Cross X B)^5,
      fun X => 5*(m 1)*(2*w X+Cross X B)^4,
      fun X => 10*(m 2)*(2*w X+Cross X B)^3,
      fun X => 10*(m 3)*(2*w X+Cross X B)^2,
      fun X => 5*(m 4)*(2*w X+Cross X B),
      fun _ => m 5,
      fun X => (15/32 : ℝ)*w X]
  have hw : Continuous (fun X : Cfg => w X) :=
    p4Q2PZ36C_half_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ36C_cross_continuous H B
  have ht : Continuous (fun X : Cfg => 2*w X+Cross X B) :=
    (continuous_const.mul hw).add hc
  have hf (i : Fin 7) : Continuous (f i) := by
    fin_cases i <;> dsimp [f] <;> fun_prop (disch := assumption)
  have hi (i : Fin 7) : Integrable (f i) haar :=
    (hf i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      (∫ Y : Cfg, (Q Y X B-w B)^5 ∂haar) =
        ∑ i : Fin 7, f i X := by
    rw [p4Q2PZ37E_originalInnerTwoStrippedFifth H X B]
    simp [f, Fin.sum_univ_succ] <;> ring
  have hSum :
      (∫ X : Cfg, (∑ i : Fin 7, f i X) ∂haar) =
        ∑ i : Fin 7, ∫ X : Cfg, f i X ∂haar :=
    integral_finset_sum (Finset.univ : Finset (Fin 7))
      (f := f) (fun i _hi => hi i)
  calc
    p4Q2PZ37E_originalTwoStrippedFifth H B =
      (∫ X : Cfg, (∑ i : Fin 7, f i X) ∂haar) := by
        unfold p4Q2PZ37E_originalTwoStrippedFifth
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
    _ = ∑ i : Fin 7, ∫ X : Cfg, f i X ∂haar := hSum
    _ = V 5 B + 5*(m 1)*V 4 B + 10*(m 2)*V 3 B +
      10*(m 3)*V 2 B + 5*(m 4)*V 1 B +
      m 5 + (15/32 : ℝ)*(∫ X : Cfg, w X ∂haar) := by
        simp [f, Fin.sum_univ_succ,
          p4Q2PZ37E_originalDoubledStripMoment, integral_const_mul] <;> ring

/-- The key missing PHYSICAL two-slab source transport:
the genuinely interacting double spatial SU(2) Haar fifth moment,
stripped of the RIGHT endpoint w(B), has precisely slope 15/16.
The auxiliary r=2 result is used only after the full Q expansion. -/
theorem p4Q2PZ37E_originalPhysicalTwoStrippedFifth_affine
    (B : Cfg) :
    p4Q2PZ37E_originalTwoStrippedFifth H B =
      p4Q2PZ37E_originalTwoStrippedFifth H I +
        (15/16 : ℝ)*w B := by
  have hLow (n : ℕ) (hn : n ≤ 4) :
      V n B = V n I := by
    simpa only [p4Q2PZ37E_originalDoubledStripMoment] using
      (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four
        H 2 n hn B)
  have hFifth : V 5 B = V 5 I+(15/16 : ℝ)*w B := by
    simpa only [p4Q2PZ37E_originalDoubledStripMoment,
      p4Q2PZ36_originalScaledStrippedFifth] using
      (p4Q2PZ36_originalDoubledSpatialFifth_affine H B)
  rw [p4Q2PZ37E_originalTwoStrippedFifth_outerExpansion H B,
    p4Q2PZ37E_originalTwoStrippedFifth_outerExpansion H I,
    hFifth, hLow 1 (by omega), hLow 2 (by omega),
    hLow 3 (by omega), hLow 4 (by omega)]
  ring

end PhysicalTwoSlabFifthSlope
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37E_originalInnerTwoStrippedFifth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37E_originalTwoStrippedFifth_outerExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37E_originalPhysicalTwoStrippedFifth_affine
