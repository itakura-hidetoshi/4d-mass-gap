import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoSlabSixthTransportV5_PZ37F
import Mathlib.Tactic

/-!
# P4-Q2-PZ37F — physical seventh jet coefficient with its sixth Haar source

The actual one- and two-slab raw Haar moments have the same right-endpoint
shift w(B). Their fifth stripped slopes are the proved physical values
15/32 and 15/16. The sixth stripped moments remain arbitrary functions of
the full boundary configuration: no factorization through w is assumed.

The original PZ37B seventh six-moment jet coefficient is first identified
with its six signed raw-moment wedges. The polynomial part then uses the
PZ37C identity with zero sixth functions, while the actual sixth functions
are retained separately in the configuration-space wedge. PZ37F's genuine
two-slab transport identifies that wedge with the four PZ37D Haar sectors.

This is an exact coefficient identity. It assumes no vanishing of the
sixth obstruction, proves no sign or nonzero witness, and makes no new
eighth-order remainder, volume-uniform, or mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37F_coefficient_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37F_coefficient_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37F_coefficient_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37F_coefficient_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37F_coefficient_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37F_coefficient_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37F_coefficient_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section PhysicalSeventhVandermonde

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
local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H
local notation "U6" => p4Q2PZ37D_originalScaledStrippedSixth H
local notation "T6" => p4Q2PZ37F_originalTwoStrippedSixth H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "F" => p4Q2PZ37D_originalMixedHaar H
local notation "P7" => p4Q2PZ37B_originalPhysicalSeventhCoefficient H

/-- General endpoint binomial for the original one-slab action. The
stripped moments are retained as actual Haar integrals at the boundary. -/
theorem p4Q2PZ37F_originalOneRaw_stripped_binomial
    (n : ℕ) (B : Cfg) :
    R1 n B = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
      ((∫ X : Cfg, (w X+Cross X B)^k ∂haar)*(w B)^(n-k)) := by
  have hc : Continuous (fun X : Cfg => w X+Cross X B) :=
    (p4Q2PZ36C_half_continuous H).add
      (p4Q2PZ36C_cross_continuous H B)
  calc
    R1 n B = (∫ X : Cfg, ((w X+Cross X B)+w B)^n ∂haar) := by
      unfold p4Q2PZ36D_originalOneRaw
      apply integral_congr_ae
      filter_upwards with X
      rw [p4Q2PZ36C_originalOneSlab_eq_rightStripped H X B]
    _ = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (∫ X : Cfg, (w X+Cross X B)^k*(w B)^(n-k) ∂haar) := by
      exact p4Q2PZ36A_originalHaar_integral_binomial H
        (fun X : Cfg => w X+Cross X B) (fun _ : Cfg => w B)
        hc continuous_const n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [integral_mul_const]

/-- General common-endpoint binomial for the complete original Q.
Continuity of its inner Haar moments justifies the outer finite sum. -/
theorem p4Q2PZ37F_originalTwoRaw_stripped_binomial
    (n : ℕ) (B : Cfg) :
    R2 n B = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
      ((∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^k ∂haar ∂haar) *
        (w B)^(n-k)) := by
  have hi (k : ℕ) (_hk : k ∈ Finset.range (n+1)) :
      Integrable (fun X : Cfg => (n.choose k : ℝ) *
        ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k))) haar := by
    have hc := p4Q2PZ37F_originalInnerTwoStripped_continuous H k B
    exact (continuous_const.mul (hc.mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    R2 n B = (∫ X : Cfg, ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) ∂haar) := by
      unfold p4Q2PZ36D_originalTwoRaw
      apply integral_congr_ae
      filter_upwards with X
      exact p4Q2PZ36D_originalTwoRaw_inner_binomial H n X B
    _ = ∑ k ∈ Finset.range (n+1),
        (∫ X : Cfg, (n.choose k : ℝ) *
          ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k)) ∂haar) := by
      exact integral_finset_sum (Finset.range (n+1))
        (f := fun k (X : Cfg) => (n.choose k : ℝ) *
          ((∫ Y : Cfg, (Q Y X B-w B)^k ∂haar)*(w B)^(n-k))) hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [integral_const_mul, integral_mul_const]

/-- The genuine fifth two-slab stripped moment uses its original raw
identity coefficient, since the physical identity has w(I)=0. -/
theorem p4Q2PZ37F_originalTwoStripFifth_eq_identityRaw (B : Cfg) :
    (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^5 ∂haar ∂haar) =
      R2 5 I + (15/16 : ℝ)*w B := by
  change p4Q2PZ37E_originalTwoStrippedFifth H B = _
  rw [p4Q2PZ37E_originalPhysicalTwoStrippedFifth_affine H B]
  simp only [p4Q2PZ37E_originalTwoStrippedFifth,
    p4Q2PZ36D_originalTwoRaw,
    p4Q2PZ35_originalHalfSpatialAction_identity_zero H, sub_zero]

/-- Actual fifth raw moment of the full two-slab Wilson action, with
the proved stripped slope q=15/16 and all lower physical coefficients. -/
theorem p4Q2PZ37F_originalTwoRaw_fifth_endpoint (B : Cfg) :
    R2 5 B =
      (w B)^5 + 5*(R2 1 I)*(w B)^4 + 10*(R2 2 I)*(w B)^3 +
        10*(R2 3 I)*(w B)^2 + (5*(R2 4 I)+(15/16 : ℝ))*w B +
        R2 5 I := by
  have h1 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 1 (by omega) B
  have h2 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 2 (by omega) B
  have h3 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 3 (by omega) B
  have h4 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 4 (by omega) B
  have h5 := p4Q2PZ37F_originalTwoStripFifth_eq_identityRaw H B
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^1 ∂haar ∂haar) = R2 1 I at h1
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^2 ∂haar ∂haar) = R2 2 I at h2
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^3 ∂haar ∂haar) = R2 3 I at h3
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^4 ∂haar ∂haar) = R2 4 I at h4
  simp only [pow_one] at h1
  rw [p4Q2PZ37F_originalTwoRaw_stripped_binomial H 5 B]
  simp [Finset.sum_range_succ, Nat.choose, h1, h2, h3, h4, h5]
  ring

/-- The one-slab sixth raw moment retains its full original stripped
sixth function. The fifth slope contributes exactly 6*p*w(B)^2. -/
theorem p4Q2PZ37F_originalOneRaw_sixth_endpoint (B : Cfg) :
    R1 6 B =
      (w B)^6 + 6*(R1 1 I)*(w B)^5 + 15*(R1 2 I)*(w B)^4 +
        20*(R1 3 I)*(w B)^3 +
        (15*(R1 4 I)+6*(15/32 : ℝ))*(w B)^2 +
        6*(R1 5 I)*w B + U6 1 B := by
  have h1 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 1 (by omega) B
  have h2 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 2 (by omega) B
  have h3 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 3 (by omega) B
  have h4 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 4 (by omega) B
  have h5 := p4Q2PZ36E_originalOneStripFifth_affine H B
  have h6 : (∫ X : Cfg, (w X+Cross X B)^6 ∂haar) = U6 1 B := by
    simp only [p4Q2PZ37D_originalScaledStrippedSixth, one_mul]
  simp only [pow_one] at h1
  rw [p4Q2PZ37F_originalOneRaw_stripped_binomial H 6 B]
  simp [Finset.sum_range_succ, Nat.choose, h1, h2, h3, h4, h5, h6]
  ring

/-- The actual two-slab sixth raw moment has the same endpoint shift.
Its arbitrary sixth stripped function is the literal double Haar T6. -/
theorem p4Q2PZ37F_originalTwoRaw_sixth_endpoint (B : Cfg) :
    R2 6 B =
      (w B)^6 + 6*(R2 1 I)*(w B)^5 + 15*(R2 2 I)*(w B)^4 +
        20*(R2 3 I)*(w B)^3 +
        (15*(R2 4 I)+6*(15/16 : ℝ))*(w B)^2 +
        6*(R2 5 I)*w B + T6 B := by
  have h1 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 1 (by omega) B
  have h2 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 2 (by omega) B
  have h3 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 3 (by omega) B
  have h4 := p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw H 4 (by omega) B
  have h5 := p4Q2PZ37F_originalTwoStripFifth_eq_identityRaw H B
  have h6 :
      (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^6 ∂haar ∂haar) = T6 B := rfl
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^1 ∂haar ∂haar) = R2 1 I at h1
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^2 ∂haar ∂haar) = R2 2 I at h2
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^3 ∂haar ∂haar) = R2 3 I at h3
  change (∫ X : Cfg, ∫ Y : Cfg, (Q Y X B-w B)^4 ∂haar ∂haar) = R2 4 I at h4
  simp only [pow_one] at h1
  rw [p4Q2PZ37F_originalTwoRaw_stripped_binomial H 6 B]
  simp [Finset.sum_range_succ, Nat.choose, h1, h2, h3, h4, h5, h6]
  ring

/-- The existing physical second Taylor row agrees in boundary
differences with the genuine complete two-slab second raw moment. -/
theorem p4Q2PZ37F_originalSecondTaylorRow_eq_rawDifference (A B : Cfg) :
    (p4Q2PK_originalOneSlabSecondActionMoment H B -
      p4Q2PK_originalOneSlabSecondActionMoment H A) +
        2*(p4Q2PK_originalMixedTwoSlabActionMoment H B -
          p4Q2PK_originalMixedTwoSlabActionMoment H A) = R2 2 B-R2 2 A := by
  rw [p4Q2PZ36H_originalTwoSecond_endpoint H B,
    p4Q2PZ36H_originalTwoSecond_endpoint H A]
  simpa only [PZ36EndpointAlgebra.second] using
    p4Q2PZ36I_originalTwoSecondTaylorRow_difference H A B

/-- Exact physical PZ37B coefficient as six genuine raw-moment wedges.
The signs are all negative because each pair has total odd degree seven. -/
theorem p4Q2PZ37F_originalPhysicalSeventhCoefficient_rawWedges
    (A B C : Cfg) :
    P7 A B C =
      -(W (R1 1) (R2 6) A B C)/720 -
        W (R1 2) (R2 5) A B C/240 -
        W (R1 3) (R2 4) A B C/144 -
        W (R1 4) (R2 3) A B C/144 -
        W (R1 5) (R2 2) A B C/240 -
        W (R1 6) (R2 1) A B C/720 := by
  unfold p4Q2PZ37B_originalPhysicalSeventhCoefficient
    p4Q2PZ1_originalSeventhFifthJetCoefficient
    p4Q2PX_originalSeventhFourthJetCoefficient
    p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37F_originalSecondTaylorRow_eq_rawDifference H A C,
    p4Q2PZ37F_originalSecondTaylorRow_eq_rawDifference H A B]
  simp only [p4Q2PZ36E_originalFirstAction_eq_negRaw,
    p4Q2PZ36E_originalSecondAction_eq_raw,
    p4Q2PZ36E_originalOneThird_eq_negRaw,
    p4Q2PZ36E_originalTwoThird_eq_negRaw,
    p4Q2PZ36E_originalOneFourth_eq_raw,
    p4Q2PZ36E_originalTwoFourth_eq_raw,
    p4Q2PZ36E_originalOneFifth_eq_raw,
    p4Q2PZ36E_originalTwoFifth_eq_raw,
    p4Q2PZ36H_originalOneFirst_endpoint H A,
    p4Q2PZ36H_originalOneFirst_endpoint H B,
    p4Q2PZ36H_originalOneFirst_endpoint H C,
    p4Q2PZ36H_originalTwoFirst_endpoint H A,
    p4Q2PZ36H_originalTwoFirst_endpoint H B,
    p4Q2PZ36H_originalTwoFirst_endpoint H C]
  ring

/-- Physical seventh jet coefficient with the actual arbitrary sixth
stripped functions. PZ37C is used only for the polynomial part, so no
unproved dependence of sixth Haar moments on w(B) is introduced. -/
theorem p4Q2PZ37F_originalPhysicalSeventhCoefficient_strippedObstruction
    (A B C : Cfg) :
    P7 A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w (fun D : Cfg => T6 D-U6 1 D) A B C/720 := by
  have hPolynomial :
      P7 A B C =
        PZ37VandermondeAlgebra.seventh
          (R1 1 I) (R1 2 I) (R1 3 I) (R1 4 I) (R1 5 I)
          (R2 1 I) (R2 2 I) (R2 3 I) (R2 4 I) (R2 5 I)
          (15/32) (15/16) (fun _ : ℝ => 0) (fun _ : ℝ => 0)
          (w A) (w B) (w C) -
            W w (fun D : Cfg => T6 D-U6 1 D) A B C/720 := by
    rw [p4Q2PZ37F_originalPhysicalSeventhCoefficient_rawWedges H A B C]
    unfold p4Q2PZ37B_originalBoundaryWedge
    simp only [p4Q2PZ36H_originalOneFirst_endpoint H A,
      p4Q2PZ36H_originalOneFirst_endpoint H B,
      p4Q2PZ36H_originalOneFirst_endpoint H C,
      p4Q2PZ36H_originalTwoFirst_endpoint H A,
      p4Q2PZ36H_originalTwoFirst_endpoint H B,
      p4Q2PZ36H_originalTwoFirst_endpoint H C,
      p4Q2PZ36H_originalOneSecond_endpoint H A,
      p4Q2PZ36H_originalOneSecond_endpoint H B,
      p4Q2PZ36H_originalOneSecond_endpoint H C,
      p4Q2PZ36H_originalTwoSecond_endpoint H A,
      p4Q2PZ36H_originalTwoSecond_endpoint H B,
      p4Q2PZ36H_originalTwoSecond_endpoint H C,
      p4Q2PZ36H_originalOneThird_endpoint H A,
      p4Q2PZ36H_originalOneThird_endpoint H B,
      p4Q2PZ36H_originalOneThird_endpoint H C,
      p4Q2PZ36H_originalTwoThird_endpoint H A,
      p4Q2PZ36H_originalTwoThird_endpoint H B,
      p4Q2PZ36H_originalTwoThird_endpoint H C,
      p4Q2PZ36H_originalOneFourth_endpoint H A,
      p4Q2PZ36H_originalOneFourth_endpoint H B,
      p4Q2PZ36H_originalOneFourth_endpoint H C,
      p4Q2PZ36H_originalTwoFourth_endpoint H A,
      p4Q2PZ36H_originalTwoFourth_endpoint H B,
      p4Q2PZ36H_originalTwoFourth_endpoint H C,
      p4Q2PZ36E_originalOneRaw_fifth_endpoint H A,
      p4Q2PZ36E_originalOneRaw_fifth_endpoint H B,
      p4Q2PZ36E_originalOneRaw_fifth_endpoint H C,
      p4Q2PZ37F_originalTwoRaw_fifth_endpoint H A,
      p4Q2PZ37F_originalTwoRaw_fifth_endpoint H B,
      p4Q2PZ37F_originalTwoRaw_fifth_endpoint H C,
      p4Q2PZ37F_originalOneRaw_sixth_endpoint H A,
      p4Q2PZ37F_originalOneRaw_sixth_endpoint H B,
      p4Q2PZ37F_originalOneRaw_sixth_endpoint H C,
      p4Q2PZ37F_originalTwoRaw_sixth_endpoint H A,
      p4Q2PZ37F_originalTwoRaw_sixth_endpoint H B,
      p4Q2PZ37F_originalTwoRaw_sixth_endpoint H C]
    unfold PZ37VandermondeAlgebra.seventh PZ37VandermondeAlgebra.wedge
      PZ37VandermondeAlgebra.first PZ37VandermondeAlgebra.second
      PZ37VandermondeAlgebra.third PZ37VandermondeAlgebra.fourth
      PZ37VandermondeAlgebra.fifth PZ37VandermondeAlgebra.sixth
    ring
  rw [hPolynomial,
    PZ37VandermondeAlgebra.seventh_vandermonde_with_sixth_obstruction]
  simp only [PZ37VandermondeAlgebra.wedge]
  ring

/-- The original physical seventh six-moment jet coefficient is exactly
-V/512 minus the four-sector sixth Haar wedge divided by 720.
No vanishing, affineness, sign, or nondegeneracy premise is used. -/
theorem p4Q2PZ37F_originalPhysicalSeventhCoefficient_fourSectorObstruction
    (A B C : Cfg) :
    P7 A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w (fun D : Cfg =>
          6*F 1 5 D + 45*F 2 4 D + 140*F 3 3 D + 225*F 4 2 D)
          A B C/720 := by
  rw [p4Q2PZ37F_originalPhysicalSeventhCoefficient_strippedObstruction H A B C,
    p4Q2PZ37F_originalTwoStrippedSixthGap_wedge_fourSectors H A B C]

end PhysicalSeventhVandermonde
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalOneRaw_stripped_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoRaw_stripped_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoStripFifth_eq_identityRaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoRaw_fifth_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalOneRaw_sixth_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalTwoRaw_sixth_endpoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalSecondTaylorRow_eq_rawDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalPhysicalSeventhCoefficient_rawWedges
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalPhysicalSeventhCoefficient_strippedObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37F_originalPhysicalSeventhCoefficient_fourSectorObstruction
