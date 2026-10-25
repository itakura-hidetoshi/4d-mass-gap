import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGlobalCenterSixthSelectionV5_PZ37G
import Mathlib.Tactic

/-!
# P4-Q2-PZ37G — original sixth-Haar obstruction after genuine SU(2) centre selection

True simultaneous centre symmetry yields ALL weighted odd moments of the
centred crossing Cross(X,B)-N_H. The ordinary Haar binomial then fixes the
odd uncentred sectors in terms of even sectors:
 F(i,3)=3N_H*F(i,2)-2N_H^3*F(i,0),
 F(i,5)=5N_H*F(i,4)-20N_H^3*F(i,2)+16N_H^5*F(i,0).

Use the previously proved original physical F(1,4) affine slope 3/32,
degree-four Haar invariance of F(1,2), and original F(3,2) invariance.
Then F(1,5) is affine in w and F(3,3) is boundary-independent.
Hence the physical sixth obstruction wedge contains only F(2,4)
and F(4,2), and the seventh physical JET coefficient retains precisely
those two genuinely unproved response sectors.

No vanishing of either survivor, no degree-eight analytic remainder,
nonzero rank, volume-uniform estimate, or continuum mass-gap assertion.
-/ 

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37G_reduction_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37G_reduction_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37G_reduction_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37G_reduction_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37G_reduction_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37G_reduction_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37G_reduction_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section SixthCenterReduced
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "F" => p4Q2PZ37D_originalMixedHaar H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "N" => p4Q2PZ37G_originalLinkCount H
local notation "I" =>
  (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))

/-- Exact binomial of the original weighted centred-crossing Haar moment.
This is the true Haar integral, not a surrogate orthogonal-polynomial model. -/
theorem p4Q2PZ37G_originalWeightedCentered_binomial
    (i n : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(Cross X B-N)^n ∂haar) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (-N)^(n-k)*F i k B := by
  let f : ℕ → Cfg → ℝ := fun k X =>
    ((n.choose k : ℝ)*(-N)^(n-k))*((w X)^i*(Cross X B)^k)
  have hw := p4Q2PZ36C_half_continuous H
  have hc := p4Q2PZ36C_cross_continuous H B
  have hf (k : ℕ) : Continuous (f k) := by
    dsimp [f]
    exact continuous_const.mul ((hw.pow i).mul (hc.pow k))
  have hi (k : ℕ) : Integrable (f k) haar :=
    (hf k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      (w X)^i*(Cross X B-N)^n =
        ∑ k ∈ Finset.range (n+1), f k X := by
    have hh : Cross X B-N = Cross X B+(-N) := by ring
    rw [hh, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp [f]
    ring
  calc
    (∫ X : Cfg, (w X)^i*(Cross X B-N)^n ∂haar) =
        (∫ X : Cfg, ∑ k ∈ Finset.range (n+1), f k X ∂haar) := by
          apply integral_congr_ae
          filter_upwards with X
          exact hPoint X
    _ = ∑ k ∈ Finset.range (n+1), (∫ X : Cfg, f k X ∂haar) :=
      integral_finset_sum (Finset.range (n+1)) (f := f) (fun k _hk => hi k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [f, integral_const_mul, p4Q2PZ37D_originalMixedHaar]

/-- Actual weighted first crossing Haar moment, fixed by global centre
reflection for every spatial Wilson power and original finite period. -/
theorem p4Q2PZ37G_originalMixedFirst_centerMean
    (i : ℕ) (B : Cfg) :
    F i 1 B = N*F i 0 B := by
  have h := p4Q2PZ37G_originalWeightedCenteredCrossing_oddHaar_zero H i 0 B
  change (∫ X : Cfg, (w X)^i*(Cross X B-N)^1 ∂haar) = 0 at h
  rw [p4Q2PZ37G_originalWeightedCentered_binomial H i 1 B] at h
  simp [Finset.sum_range_succ, Nat.choose] at h
  linarith

/-- All original weighted third crossing Haar moments are determined by
true even moments, not by posterior independence. -/
theorem p4Q2PZ37G_originalMixedThird_evenSectors
    (i : ℕ) (B : Cfg) :
    F i 3 B = 3*N*F i 2 B-2*N^3*F i 0 B := by
  have h := p4Q2PZ37G_originalWeightedCenteredCrossing_oddHaar_zero H i 1 B
  change (∫ X : Cfg, (w X)^i*(Cross X B-N)^3 ∂haar) = 0 at h
  rw [p4Q2PZ37G_originalWeightedCentered_binomial H i 3 B] at h
  simp [Finset.sum_range_succ, Nat.choose] at h
  rw [p4Q2PZ37G_originalMixedFirst_centerMean H i B] at h
  nlinarith

/-- The genuine fifth crossing Haar moment is exactly an even-sector
combination for any original spatial Wilson weight w^i. -/
theorem p4Q2PZ37G_originalMixedFifth_evenSectors
    (i : ℕ) (B : Cfg) :
    F i 5 B = 5*N*F i 4 B-20*N^3*F i 2 B+16*N^5*F i 0 B := by
  have h := p4Q2PZ37G_originalWeightedCenteredCrossing_oddHaar_zero H i 2 B
  change (∫ X : Cfg, (w X)^i*(Cross X B-N)^5 ∂haar) = 0 at h
  rw [p4Q2PZ37G_originalWeightedCentered_binomial H i 5 B] at h
  simp [Finset.sum_range_succ, Nat.choose] at h
  rw [p4Q2PZ37G_originalMixedFirst_centerMean H i B,
    p4Q2PZ37G_originalMixedThird_evenSectors H i B] at h
  nlinarith

/-- First selected sixth Haar sector F(1,5) has an exact, PHYSICAL
affine dependence fixed by Schur's original F(1,4) slope 3/32. -/
theorem p4Q2PZ37G_originalF15_affine
    (B : Cfg) :
    F 1 5 B = F 1 5 I + (15/32 : ℝ)*N*w B := by
  have h5B := p4Q2PZ37G_originalMixedFifth_evenSectors H 1 B
  have h5I := p4Q2PZ37G_originalMixedFifth_evenSectors H 1 I
  have h14 : F 1 4 B = F 1 4 I + (3/32 : ℝ)*w B := by
    simpa only [p4Q2PZ37D_originalMixedHaar,
      p4Q2PZ22_originalSpatialCrossingFourthHaar, pow_one] using
      (p4Q2PZ36_originalF14_affine H B)
  have h12 := p4Q2PZ36A_originalMixedMoment_invariant_le_four H 1 2 (by omega) B
  change F 1 2 B = F 1 2 I at h12
  have h10 : F 1 0 B = F 1 0 I := rfl
  rw [h5B, h5I, h14, h12, h10]
  ring

/-- The F(3,3) sector has no original right-boundary response, by
true centre selection plus the already proved all-period F(3,2) Ward. -/
theorem p4Q2PZ37G_originalF33_boundaryInvariant
    (B : Cfg) :
    F 3 3 B = F 3 3 I := by
  rw [p4Q2PZ37G_originalMixedThird_evenSectors H 3 B,
    p4Q2PZ37G_originalMixedThird_evenSectors H 3 I]
  have h32 := p4Q2PZ32_originalF32_Haar_boundaryInvariant H B
  change F 3 2 B = F 3 2 I at h32
  rw [h32]
  rfl

/-- The original sixth obstruction loses precisely its known affine
and constant sectors under alternating with the ORIGINAL half action.
The remaining two even-centre sectors are NOT assumed to vanish. -/
theorem p4Q2PZ37G_originalSixthWedge_twoEvenSectors
    (A B C : Cfg) :
    W w
      (fun D : Cfg =>
        6*F 1 5 D + 45*F 2 4 D + 140*F 3 3 D + 225*F 4 2 D)
      A B C =
    W w (fun D : Cfg => 45*F 2 4 D + 225*F 4 2 D) A B C := by
  unfold p4Q2PZ37B_originalBoundaryWedge
  dsimp only
  rw [p4Q2PZ37G_originalF15_affine H A,
    p4Q2PZ37G_originalF15_affine H B,
    p4Q2PZ37G_originalF15_affine H C,
    p4Q2PZ37G_originalF33_boundaryInvariant H A,
    p4Q2PZ37G_originalF33_boundaryInvariant H B,
    p4Q2PZ37G_originalF33_boundaryInvariant H C]
  ring

/-- Original physical seventh six-moment jet coefficient, now exactly
two authentic SU(2) sixth Haar sectors, not an assumed -V/512. -/
theorem p4Q2PZ37G_originalPhysicalSeventhJet_twoEvenObstructions
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w (fun D : Cfg => 45*F 2 4 D + 225*F 4 2 D) A B C/720 := by
  rw [p4Q2PZ37F_originalPhysicalSeventhCoefficient_fourSectorObstruction H A B C,
    p4Q2PZ37G_originalSixthWedge_twoEvenSectors H A B C]

end SixthCenterReduced
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalWeightedCentered_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalMixedFirst_centerMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalMixedThird_evenSectors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalMixedFifth_evenSectors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalF15_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalF33_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalSixthWedge_twoEvenSectors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37G_originalPhysicalSeventhJet_twoEvenObstructions
