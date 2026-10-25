import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoSlabFifthSlopeV5_PZ37E
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityContinuity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37F — genuine two-slab sixth stripped Haar transport

The original interacting Q keeps the middle half-spatial action twice.
The inner fifth affine correction contributes a genuine mixed outer
integral; its boundary independence is proved, not replaced by zero.
The sixth inner marginal is retained with its compact-domain continuity.

The actual two-slab sixth moment differs from the auxiliary r=2 sixth
moment by a constant PLUS (45/8)*m1*w(B). Only their wedges with w agree.
This transports PZ37D's four-sector sixth obstruction to the physical
two-slab moment without assuming that obstruction vanishes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37F_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37F_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37F_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37F_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37F_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37F_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37F_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalTwoSlabSixthTransport
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "m" => p4Q2PZ36C_originalStripMoment H
local notation "V" => p4Q2PZ37E_originalDoubledStripMoment H
local notation "U6" => p4Q2PZ37D_originalScaledStrippedSixth H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "F" => p4Q2PZ37D_originalMixedHaar H

/-- The true stripped sixth moment of the complete interacting Q. -/
noncomputable def p4Q2PZ37F_originalTwoStrippedSixth (B : Cfg) : ℝ :=
  ∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^6 ∂haar ∂haar

/-- Compact original Haar integration preserves continuity in the boundary.
No sixth-moment affineness or factorization through w is asserted. -/
theorem p4Q2PZ37F_originalScaledStripMoment_continuous (r : ℝ) (n : ℕ) :
    Continuous (fun B : Cfg => ∫ X : Cfg, (r*w X+Cross X B)^n ∂haar) := by
  apply continuous_integral_compact_domain haar
    (fun B X : Cfg => (r*w X+Cross X B)^n)
  have hw : Continuous (fun p : Cfg × Cfg => w p.2) :=
    (p4Q2PZ36C_half_continuous H).comp continuous_snd
  have hc : Continuous (fun p : Cfg × Cfg => Cross p.2 p.1) := by
    simpa only [Function.comp_def] using
      (p4Q2IW_originalWilsonCrossingAction_continuous H).comp
        (continuous_snd.prodMk continuous_fst)
  exact ((continuous_const.mul hw).add hc).pow n

/-- Continuity of the actual inner stripped Q moment at every finite degree. -/
theorem p4Q2PZ37F_originalInnerTwoStripped_continuous
    (n : ℕ) (B : Cfg) :
    Continuous (fun X : Cfg => ∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) := by
  apply continuous_integral_compact_domain haar
    (fun X Y : Cfg => (Q Y X B-w B)^n)
  have hwY : Continuous (fun p : Cfg × Cfg => w p.2) :=
    (p4Q2PZ36C_half_continuous H).comp continuous_snd
  have hcYX : Continuous (fun p : Cfg × Cfg => Cross p.2 p.1) := by
    simpa only [Function.comp_def] using
      (p4Q2IW_originalWilsonCrossingAction_continuous H).comp
        (continuous_snd.prodMk continuous_fst)
  have hwX : Continuous (fun p : Cfg × Cfg => w p.1) :=
    (p4Q2PZ36C_half_continuous H).comp continuous_fst
  have hcXB : Continuous (fun p : Cfg × Cfg => Cross p.1 B) :=
    (p4Q2PZ36C_cross_continuous H B).comp continuous_fst
  have heq :
      Function.uncurry (fun X Y : Cfg => (Q Y X B-w B)^n) =
      (fun p : Cfg × Cfg =>
        ((w p.2+Cross p.2 p.1)+(2*w p.1+Cross p.1 B))^n) := by
    funext p
    exact congrArg (fun t : ℝ => t^n)
      (p4Q2PZ36C_originalTwoSlab_strip_eq H p.2 p.1 B)
  rw [heq]
  exact ((hwY.add hcYX).add ((continuous_const.mul hwX).add hcXB)).pow n

/-- The original single-slab stripped sixth is precisely the r=1 observable. -/
theorem p4Q2PZ37F_originalOneStrippedSixth_eq (B : Cfg) :
    (∫ X : Cfg, (S X B-w B)^6 ∂haar) = U6 1 B := by
  unfold p4Q2PZ37D_originalScaledStrippedSixth
  apply integral_congr_ae
  filter_upwards with X
  rw [p4Q2PZ36C_originalOneSlab_eq_rightStripped H X B]
  ring

/-- All seven binomial sectors, including the true fifth affine correction
and the uncomputed sixth inner Haar marginal, of the complete Q. -/
theorem p4Q2PZ37F_originalInnerTwoStrippedSixth (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B-w B)^6 ∂haar) =
      (2*w X+Cross X B)^6 +
      6*(m 1)*(2*w X+Cross X B)^5 +
      15*(m 2)*(2*w X+Cross X B)^4 +
      20*(m 3)*(2*w X+Cross X B)^3 +
      15*(m 4)*(2*w X+Cross X B)^2 +
      6*(m 5)*(2*w X+Cross X B) +
      (45/16 : ℝ)*w X*(2*w X+Cross X B) + U6 1 X := by
  let t : ℝ := 2*w X+Cross X B
  have hc : Continuous (fun Y : Cfg => w Y+Cross Y X) :=
    (p4Q2PZ36C_half_continuous H).add (p4Q2PZ36C_cross_continuous H X)
  have hLow (k : ℕ) (hk : k ≤ 4) :
      (∫ Y : Cfg, (w Y+Cross Y X)^k ∂haar) = m k := by
    simpa only [one_mul, p4Q2PZ36C_originalStripMoment] using
      (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four H 1 k hk X)
  have hFifth :
      (∫ Y : Cfg, (w Y+Cross Y X)^5 ∂haar) =
        m 5 + (15/32 : ℝ)*w X := by
    simpa only [one_mul, mul_one, p4Q2PZ36_originalScaledStrippedFifth,
      p4Q2PZ36C_originalStripMoment] using
      (p4Q2PZ36_originalScaledStrippedFifth_affine H 1 X)
  have hFirst : (∫ Y : Cfg, w Y+Cross Y X ∂haar) = m 1 := by
    simpa only [pow_one] using hLow 1 (by omega)
  have hSixth : (∫ Y : Cfg, (w Y+Cross Y X)^6 ∂haar) = U6 1 X := by
    simp only [p4Q2PZ37D_originalScaledStrippedSixth, one_mul]
  calc
    (∫ Y : Cfg, (Q Y X B-w B)^6 ∂haar) =
      (∫ Y : Cfg, ((w Y+Cross Y X)+t)^6 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with Y
        rw [p4Q2PZ36C_originalTwoSlab_strip_eq H Y X B]
    _ = ∑ k ∈ Finset.range 7, ((6 : ℕ).choose k : ℝ) *
        ((∫ Y : Cfg, (w Y+Cross Y X)^k ∂haar)*t^(6-k)) := by
      rw [p4Q2PZ36A_originalHaar_integral_binomial H
        (fun Y : Cfg => w Y+Cross Y X) (fun _ : Cfg => t)
        hc continuous_const 6]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [integral_mul_const]
    _ = (2*w X+Cross X B)^6 +
      6*(m 1)*(2*w X+Cross X B)^5 +
      15*(m 2)*(2*w X+Cross X B)^4 +
      20*(m 3)*(2*w X+Cross X B)^3 +
      15*(m 4)*(2*w X+Cross X B)^2 +
      6*(m 5)*(2*w X+Cross X B) +
      (45/16 : ℝ)*w X*(2*w X+Cross X B) + U6 1 X := by
      dsimp [t]
      simp [Finset.sum_range_succ, Nat.choose, hFirst,
        hLow 2 (by omega), hLow 3 (by omega), hLow 4 (by omega),
        hFifth, hSixth]
      ring

/-- The full physical outer integral, with every affine-correction term
and the integrated sixth marginal present. -/
theorem p4Q2PZ37F_originalTwoStrippedSixth_outerExpansion (B : Cfg) :
    p4Q2PZ37F_originalTwoStrippedSixth H B =
      V 6 B + 6*(m 1)*V 5 B + 15*(m 2)*V 4 B +
      20*(m 3)*V 3 B + 15*(m 4)*V 2 B + 6*(m 5)*V 1 B +
      (45/16 : ℝ)*(∫ X : Cfg, w X*(2*w X+Cross X B) ∂haar) +
      (∫ X : Cfg, U6 1 X ∂haar) := by
  let f : Fin 8 → Cfg → ℝ :=
    ![fun X => (2*w X+Cross X B)^6,
      fun X => 6*(m 1)*(2*w X+Cross X B)^5,
      fun X => 15*(m 2)*(2*w X+Cross X B)^4,
      fun X => 20*(m 3)*(2*w X+Cross X B)^3,
      fun X => 15*(m 4)*(2*w X+Cross X B)^2,
      fun X => 6*(m 5)*(2*w X+Cross X B),
      fun X => (45/16 : ℝ)*(w X*(2*w X+Cross X B)),
      fun X => U6 1 X]
  have hw : Continuous (fun X : Cfg => w X) := p4Q2PZ36C_half_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) := p4Q2PZ36C_cross_continuous H B
  have ht : Continuous (fun X : Cfg => 2*w X+Cross X B) :=
    (continuous_const.mul hw).add hc
  have hu : Continuous (fun X : Cfg => U6 1 X) :=
    p4Q2PZ37F_originalScaledStripMoment_continuous H 1 6
  have hf (i : Fin 8) : Continuous (f i) := by
    fin_cases i <;> dsimp [f] <;> fun_prop (disch := assumption)
  have hi (i : Fin 8) : Integrable (f i) haar :=
    (hf i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      (∫ Y : Cfg, (Q Y X B-w B)^6 ∂haar) = ∑ i : Fin 8, f i X := by
    rw [p4Q2PZ37F_originalInnerTwoStrippedSixth H X B]
    simp [f, Fin.sum_univ_succ]
    ring
  calc
    p4Q2PZ37F_originalTwoStrippedSixth H B =
      (∫ X : Cfg, (∑ i : Fin 8, f i X) ∂haar) := by
        unfold p4Q2PZ37F_originalTwoStrippedSixth
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
    _ = ∑ i : Fin 8, ∫ X : Cfg, f i X ∂haar :=
      integral_finset_sum (Finset.univ : Finset (Fin 8))
        (f := f) (fun i _hi => hi i)
    _ = V 6 B + 6*(m 1)*V 5 B + 15*(m 2)*V 4 B +
      20*(m 3)*V 3 B + 15*(m 4)*V 2 B + 6*(m 5)*V 1 B +
      (45/16 : ℝ)*(∫ X : Cfg, w X*(2*w X+Cross X B) ∂haar) +
      (∫ X : Cfg, U6 1 X ∂haar) := by
        simp [f, Fin.sum_univ_succ,
          p4Q2PZ37E_originalDoubledStripMoment, integral_const_mul]
        ring

/-- The inner fifth affine correction is boundary-independent after true
outer Haar integration. Its value is not asserted to be zero. -/
theorem p4Q2PZ37F_originalFifthCorrection_invariant (B : Cfg) :
    (∫ X : Cfg, w X*(2*w X+Cross X B) ∂haar) =
      (∫ X : Cfg, w X*(2*w X+Cross X I) ∂haar) := by
  have hw : Continuous (fun X : Cfg => w X) := p4Q2PZ36C_half_continuous H
  have hExpand (D : Cfg) :
      (∫ X : Cfg, w X*(2*w X+Cross X D) ∂haar) =
        2*(∫ X : Cfg, (w X)^2 ∂haar) +
          (∫ X : Cfg, w X*Cross X D ∂haar) := by
    have hi1 : Integrable (fun X : Cfg => 2*(w X)^2) haar :=
      (continuous_const.mul (hw.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun X : Cfg => w X*Cross X D) haar :=
      (hw.mul (p4Q2PZ36C_cross_continuous H D)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      (∫ X : Cfg, w X*(2*w X+Cross X D) ∂haar) =
        (∫ X : Cfg, 2*(w X)^2+w X*Cross X D ∂haar) := by
          apply integral_congr_ae
          filter_upwards with X
          ring
      _ = _ := by rw [integral_add hi1 hi2, integral_const_mul]
  have hCross := p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant H 1 B
  simp only [pow_one] at hCross
  rw [hExpand B, hExpand I, hCross]

/-- Strong source-level transport: the genuine two-slab-minus-auxiliary
sixth response has the explicitly retained affine boundary variation. -/
theorem p4Q2PZ37F_originalTwoStrippedSixth_auxiliaryDifference
    (A B : Cfg) :
    (p4Q2PZ37F_originalTwoStrippedSixth H B-U6 2 B) -
      (p4Q2PZ37F_originalTwoStrippedSixth H A-U6 2 A) =
        (45/8 : ℝ)*(m 1)*(w B-w A) := by
  have hLow (n : ℕ) (hn : n ≤ 4) (D : Cfg) : V n D = V n I := by
    simpa only [p4Q2PZ37E_originalDoubledStripMoment] using
      (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four H 2 n hn D)
  have hFifth (D : Cfg) : V 5 D = V 5 I+(15/16 : ℝ)*w D := by
    simpa only [p4Q2PZ37E_originalDoubledStripMoment,
      p4Q2PZ36_originalScaledStrippedFifth] using
      (p4Q2PZ36_originalDoubledSpatialFifth_affine H D)
  have hSixth (D : Cfg) : V 6 D = U6 2 D := rfl
  rw [p4Q2PZ37F_originalTwoStrippedSixth_outerExpansion H B,
    p4Q2PZ37F_originalTwoStrippedSixth_outerExpansion H A,
    hSixth B, hSixth A, hFifth B, hFifth A,
    hLow 1 (by omega) B, hLow 1 (by omega) A,
    hLow 2 (by omega) B, hLow 2 (by omega) A,
    hLow 3 (by omega) B, hLow 3 (by omega) A,
    hLow 4 (by omega) B, hLow 4 (by omega) A,
    p4Q2PZ37F_originalFifthCorrection_invariant H B,
    p4Q2PZ37F_originalFifthCorrection_invariant H A]
  ring

/-- Only after alternating with the actual endpoint action does the
constant-plus-affine transport correction disappear. -/
theorem p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_transport
    (A B C : Cfg) :
    W w (fun D : Cfg => p4Q2PZ37F_originalTwoStrippedSixth H D-U6 1 D) A B C =
      W w (fun D : Cfg => U6 2 D-U6 1 D) A B C := by
  have hDiff (D : Cfg) :
      p4Q2PZ37F_originalTwoStrippedSixth H D-U6 1 D -
        (p4Q2PZ37F_originalTwoStrippedSixth H A-U6 1 A) =
      (U6 2 D-U6 1 D) - (U6 2 A-U6 1 A) +
        (45/8 : ℝ)*(m 1)*(w D-w A) := by
    have hD := p4Q2PZ37F_originalTwoStrippedSixth_auxiliaryDifference H A D
    linarith
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [hDiff B, hDiff C]
  ring

/-- The exact requested physical sixth-Haar obstruction, reduced to four
genuine mixed original SU(2) Haar sectors. No vanishing hypothesis. -/
theorem p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_fourSectors
    (A B C : Cfg) :
    W w (fun D : Cfg => p4Q2PZ37F_originalTwoStrippedSixth H D-U6 1 D) A B C =
      W w (fun D : Cfg =>
        6*F 1 5 D + 45*F 2 4 D + 140*F 3 3 D + 225*F 4 2 D) A B C := by
  rw [p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_transport H A B C]
  exact p4Q2PZ37D_originalScaledSixthGap_wedge_fourSectors H A B C

end OriginalTwoSlabSixthTransport
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalScaledStripMoment_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalInnerTwoStripped_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalOneStrippedSixth_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalInnerTwoStrippedSixth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoStrippedSixth_outerExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalFifthCorrection_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoStrippedSixth_auxiliaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_fourSectors
