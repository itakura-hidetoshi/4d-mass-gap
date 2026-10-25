import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoSlabStrippedTransportV5_PZ36C
import Mathlib.Tactic

/-!
# PZ36D — literal one-/two-slab common-endpoint moment transport

The coefficients below are actual original Haar moments at the identity
boundary, never free algebraic parameters. PZ36C retains the full middle
spatial action. Both original moment families have the same endpoint
binomial through degree four. No posterior factorization, additional
moment assumption, new axiom, sorry, admit, or native_decide.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36D_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36D_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36D_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36D_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36D_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36D_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36D_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalEndpointMoments
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

/-- Genuine raw one-slab moment, including the true endpoint action. -/
noncomputable def p4Q2PZ36D_originalOneRaw (n : ℕ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (S X B)^n ∂haar

/-- Genuine iterated two-slab Haar moment with the complete original Q. -/
noncomputable def p4Q2PZ36D_originalTwoRaw (n : ℕ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (∫ Y : Cfg, (Q Y X B)^n ∂haar) ∂haar

local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H

@[simp] theorem p4Q2PZ36D_originalOneRaw_zero (B : Cfg) : R1 0 B = 1 := by
  simp [p4Q2PZ36D_originalOneRaw]

@[simp] theorem p4Q2PZ36D_originalTwoRaw_zero (B : Cfg) : R2 0 B = 1 := by
  simp [p4Q2PZ36D_originalTwoRaw]

/-- The actual one-slab stripped moment equals its genuine identity moment. -/
theorem p4Q2PZ36D_originalOneStrip_eq_identityRaw
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (w X+Cross X B)^n ∂haar) = R1 n I := by
  calc
    (∫ X : Cfg, (w X+Cross X B)^n ∂haar) =
        (∫ X : Cfg, (w X+Cross X I)^n ∂haar) := by
      simpa only [one_mul] using
        (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four H 1 n hn B)
    _ = R1 n I := by
      unfold p4Q2PZ36D_originalOneRaw
      apply integral_congr_ae
      filter_upwards with X
      rw [p4Q2PS_originalOneSlabAction_eq_rightStripped H X I]
      change (w X+Cross X I)^n = (w X+Cross X I+w I)^n
      rw [p4Q2PZ35_originalHalfSpatialAction_identity_zero H, add_zero]

/-- One-slab endpoint binomial with original Haar coefficients. -/
theorem p4Q2PZ36D_originalOneRaw_endpoint_binomial
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    R1 n B = ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℝ)*(R1 k I*(w B)^(n-k)) := by
  have hc : Continuous (fun X : Cfg => w X+Cross X B) :=
    (p4Q2PZ36C_half_continuous H).add (p4Q2PZ36C_cross_continuous H B)
  have hPoint (X : Cfg) : S X B = (w X+Cross X B)+w B :=
    p4Q2PS_originalOneSlabAction_eq_rightStripped H X B
  calc
    R1 n B = (∫ X : Cfg, ((w X+Cross X B)+w B)^n ∂haar) := by
      unfold p4Q2PZ36D_originalOneRaw
      simp_rw [hPoint]
    _ = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*
        ((∫ X : Cfg, (w X+Cross X B)^k ∂haar)*(w B)^(n-k)) := by
      rw [p4Q2PZ36A_originalHaar_integral_binomial H
        (fun X : Cfg => w X+Cross X B) (fun _ : Cfg => w B)
        hc continuous_const n]
      apply Finset.sum_congr rfl
      intro k _hk
      change (n.choose k : ℝ)*
        (∫ X : Cfg, (w X+Cross X B)^k*(w B)^(n-k) ∂haar) = _
      rw [integral_mul_const]
    _ = ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ)*(R1 k I*(w B)^(n-k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk4 : k ≤ 4 := by
        have hk' := Finset.mem_range.mp hk
        omega
      rw [p4Q2PZ36D_originalOneStrip_eq_identityRaw H k hk4 B]

/-- Inner raw Q moment: the removed right endpoint is a scalar,
whereas the full middle action remains in Q-w(B). -/
theorem p4Q2PZ36D_originalTwoRaw_inner_binomial
    (n : ℕ) (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B)^n ∂haar) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*
        ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) := by
  have hc : Continuous (fun Y : Cfg => Q Y X B-w B) := by
    have heq : (fun Y : Cfg => Q Y X B-w B) =
        (fun Y : Cfg => (w Y+Cross Y X)+(2*w X+Cross X B)) := by
      funext Y
      exact p4Q2PZ36C_originalTwoSlab_strip_eq H Y X B
    rw [heq]
    exact ((p4Q2PZ36C_half_continuous H).add
      (p4Q2PZ36C_cross_continuous H X)).add continuous_const
  calc
    (∫ Y : Cfg, (Q Y X B)^n ∂haar) =
        (∫ Y : Cfg, ((Q Y X B-w B)+w B)^n ∂haar) := by
      apply integral_congr_ae
      filter_upwards with Y
      rw [sub_add_cancel]
    _ = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*
        ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) := by
      rw [p4Q2PZ36A_originalHaar_integral_binomial H
        (fun Y : Cfg => Q Y X B-w B) (fun _ : Cfg => w B)
        hc continuous_const n]
      apply Finset.sum_congr rfl
      intro k _hk
      change (n.choose k : ℝ)*
        (∫ Y : Cfg, (Q Y X B-w B)^k*(w B)^(n-k) ∂haar) = _
      rw [integral_mul_const]

/-- The previously missing full original TWO-slab endpoint transport.
Every coefficient is its actual identity-boundary double-Haar moment. -/
theorem p4Q2PZ36D_originalTwoRaw_endpoint_binomial
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    R2 n B = ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℝ)*(R2 k I*(w B)^(n-k)) := by
  have hk4 (k : ℕ) (hk : k ∈ Finset.range (n+1)) : k ≤ 4 := by
    have hk' := Finset.mem_range.mp hk
    omega
  have hi (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      Integrable (fun X : Cfg => (n.choose k : ℝ)*
        ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k))) haar := by
    have hc := p4Q2PZ36C_originalInnerStrip_continuous H k (hk4 k hk) B
    exact (continuous_const.mul (hc.mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    R2 n B = (∫ X : Cfg, ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ)*
          ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) ∂haar) := by
      unfold p4Q2PZ36D_originalTwoRaw
      apply integral_congr_ae
      filter_upwards with X
      exact p4Q2PZ36D_originalTwoRaw_inner_binomial H n X B
    _ = ∑ k ∈ Finset.range (n+1),
        (∫ X : Cfg, (n.choose k : ℝ)*
          ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) ∂haar) := by
      exact integral_finset_sum (Finset.range (n+1))
        (f := fun k (X : Cfg) => (n.choose k : ℝ)*
          ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k))) hi
    _ = ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ)*(R2 k I*(w B)^(n-k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul, integral_mul_const,
        p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H k (hk4 k hk) B]
      rfl

end OriginalEndpointMoments
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalOneRaw_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalTwoRaw_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalOneStrip_eq_identityRaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalOneRaw_endpoint_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalTwoRaw_inner_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36D_originalTwoRaw_endpoint_binomial
