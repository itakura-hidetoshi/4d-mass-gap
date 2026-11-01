import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAntipodalChordalHaarThresholdV5_PZ37ADN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADO — two-radius antipodal original Haar obstruction

ADN proved m(r) ≤ 1/2 for r² ≤ 2, and m(r) ≥ 1/2 for r² > 2
using the EXACT normalized SU(2) Wilson-feature chord, Haar, and
genuine central antipode z = -1.

This append-only file obtains a different-radius antipodal disjointness
rule: when r,s>0 and r²+s²≤4, the TRUE balls B_J(1,r) and B_J(z,s)
are disjoint, so m(r)+m(s)≤1 by normalized compact Haar.

The previously proved original radius-5/4 low-energy cap mass
m(5/4)≥1/8 therefore forces m(r)≤7/8 whenever 0<r and r²≤39/16.
For every 0<r<2, a positive antipodal ball of radius 2-r
forces m(r)<1. No uniform small-r lower mass formula is invented.

In the genuine original periodic spatial geometry, there are at least
FOUR distinct actual time-zero spatial vertices (origin and the three
distinct unit-axis directions), and THREE spatial link directions.
Hence card(Link_H)≥12, using the actual ZMod(2(H+1)) side length.
The proof uses Nat.card_prod to avoid dependent Fintype-instance
normalization artifacts, not an assumed cardinality floor.

ADM+ADN's genuine full all-link pair-Haar box law now implies
ν_H(B_D(a,r)) ≤ (7/8)^(2 card(Link_H)) ≤ (7/8)^24 < 1/17
for every actual finite H and every 0<r with r²≤39/16.
In particular this holds at r=3/2, STRICTLY beyond ADN's √2 bound.
ADI therefore proves the unchanged physical 68-sufficient-condition
numeric obstruction for the SAME genuine original covariance and cap.

This says nothing about numerical small-r positive lower masses,
genuine physical covariance Lipschitz constants, uniformly stable
covariance at radius 3/2, H-uniform coercivity, or continuum 4D
Yang--Mills mass gap. The physical source, receiver, Perron/transfer,
two posteriors, original Haar law, and theorem root are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" => normalizedCompactHaar G
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

local instance p4Q2PZ37ADO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADO_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The identity and genuine central-antipode chord squares SUM to FOUR
for every original SU(2) group element, not just along a test subset. -/
theorem p4Q2PZ37ADO_twoAntipodalChordSquares_eq_four (g : G) :
    dJ (1 : G) g ^ 2 + dJ z g ^ 2 = 4 := by
  rw [p4Q2PZ37ADN_identityChordal_sq,
    p4Q2PZ37ADN_antipodalChordal_sq]
  ring

/-- The ORIGINAL identity and central-antipode chordal balls with
different radii r,s cannot overlap if r²+s²≤4. -/
theorem p4Q2PZ37ADO_twoRadiusAntipodalBalls_disjoint
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hSquares : r ^ 2 + s ^ 2 ≤ 4) :
    Disjoint (BallJ (1 : G) r) (BallJ z s) := by
  apply Set.disjoint_left.mpr
  intro g hgOne hgAnt
  have hOne : dJ (1 : G) g < r := hgOne
  have hAnt : dJ z g < s := hgAnt
  have hOneNN := p4Q2PZ37ADK_trueChordalDistance_nonneg (1 : G) g
  have hAntNN := p4Q2PZ37ADK_trueChordalDistance_nonneg z g
  have hOneSq : dJ (1 : G) g ^ 2 < r ^ 2 := by
    have hProd : 0 < (r - dJ (1 : G) g) * (r + dJ (1 : G) g) :=
      mul_pos (sub_pos.mpr hOne)
        (add_pos_of_pos_of_nonneg hr hOneNN)
    nlinarith
  have hAntSq : dJ z g ^ 2 < s ^ 2 := by
    have hProd : 0 < (s - dJ z g) * (s + dJ z g) :=
      mul_pos (sub_pos.mpr hAnt)
        (add_pos_of_pos_of_nonneg hs hAntNN)
    nlinarith
  have hSum := p4Q2PZ37ADO_twoAntipodalChordSquares_eq_four g
  linarith

/-- Distinct-radius antipodal balls in the TRUE original SU(2)
normalized Haar satisfy m(r)+m(s)≤1. -/
theorem p4Q2PZ37ADO_twoRadiusHaarMass_sum_le_one
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hSquares : r ^ 2 + s ^ 2 ≤ 4) :
    m r + m s ≤ 1 := by
  have hd := p4Q2PZ37ADO_twoRadiusAntipodalBalls_disjoint
    r s hr hs hSquares
  have hUnion :
      Measure.real haar (BallJ (1 : G) r ∪ BallJ z s) =
        Measure.real haar (BallJ (1 : G) r) +
          Measure.real haar (BallJ z s) :=
    measureReal_union hd
      (p4Q2PZ37ADK_trueChordalBall_isOpen z s).measurableSet
  have hBound :
      Measure.real haar (BallJ (1 : G) r ∪ BallJ z s) ≤ 1 :=
    measureReal_le_one
  rw [hUnion] at hBound
  change m r + Measure.real haar (BallJ z s) ≤ 1 at hBound
  rw [p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial z s] at hBound
  exact hBound

/-- At every ORIGINAL radius 0<r<2, some genuine antipodal ball
still has positive Haar mass, so m(r) is STRICTLY less than one.
No numerical small-radius lower mass is assumed. -/
theorem p4Q2PZ37ADO_radialMass_lt_one_below_two
    (r : ℝ) (hr : 0 < r) (hr2 : r < 2) :
    m r < 1 := by
  have hs : 0 < 2 - r := by linarith
  have hProd : 0 ≤ r * (2 - r) :=
    mul_nonneg hr.le (sub_nonneg.mpr hr2.le)
  have hSq : r ^ 2 + (2 - r) ^ 2 ≤ 4 := by nlinarith
  have hSum := p4Q2PZ37ADO_twoRadiusHaarMass_sum_le_one
    r (2 - r) hr hs hSq
  have hPos :=
    p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos (2 - r) hs
  linarith

/-- Calibrate the genuine original radial Haar mass from above
in the larger explicit radius regime r²≤39/16, by translating
the already PROVED ADK radius-5/4 cap of mass at least 1/8. -/
theorem p4Q2PZ37ADO_radialMass_le_sevenEighths
    (r : ℝ) (hr : 0 < r) (hrSq : r ^ 2 ≤ (39 / 16 : ℝ)) :
    m r ≤ (7 / 8 : ℝ) := by
  have hSquares : r ^ 2 + (5 / 4 : ℝ) ^ 2 ≤ 4 := by
    nlinarith only [hrSq]
  have hSum := p4Q2PZ37ADO_twoRadiusHaarMass_sum_le_one
    r (5 / 4) hr (by norm_num) hSquares
  have hOld : (1 / 8 : ℝ) ≤ m (5 / 4) := by
    change (1 / 8 : ℝ) ≤
      Measure.real haar (BallJ (1 : G) (5 / 4))
    exact p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth
      (1 : G) (5 / 4) (by norm_num)
  linarith

/-- At one explicit radius above the ADN √2 transition the
genuine ORIGINAL Haar mass has both numerical bounds. -/
theorem p4Q2PZ37ADO_radialMass_threeHalves_interval :
    (1 / 2 : ℝ) ≤ m (3 / 2) ∧ m (3 / 2) ≤ (7 / 8 : ℝ) := by
  constructor
  · exact p4Q2PZ37ADN_radiusThreeHalves_mass_ge_half
  · exact p4Q2PZ37ADO_radialMass_le_sevenEighths
      (3 / 2) (by norm_num) (by norm_num)

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Vertex" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "Direction" => PeriodicHypercubicEvenSpatialDirection
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "K" => p4Q2PZ37ADF_originalTransferPlaquetteFCBound H

local instance p4Q2PZ37ADO_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADO_vertices : Fintype Vertex := Fintype.ofFinite _
local instance p4Q2PZ37ADO_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- FOUR actual zero-time spatial vertices: the origin and
three coordinate-unit vertices. Every side L=2(H+1) is at least two. -/
def p4Q2PZ37ADO_fourSpatialVertices (k : Fin 4) : Vertex :=
  ⟨fun i : Fin 4 => if i = 0 then 0 else if i = k then 1 else 0, by
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩

/-- The four original lattice vertices are distinct, uniformly
at every H, including the smallest physical even torus. -/
theorem p4Q2PZ37ADO_fourSpatialVertices_injective :
    Function.Injective (p4Q2PZ37ADO_fourSpatialVertices H) := by
  have hLength : PeriodicHypercubicEvenSideLength H ≠ 1 := by
    unfold PeriodicHypercubicEvenSideLength
    omega
  have hOne :
      (1 : ZMod (PeriodicHypercubicEvenSideLength H)) ≠ 0 := by
    intro hh
    exact hLength (ZMod.one_eq_zero_iff.mp hh)
  intro k l h
  by_cases hk : k = 0
  · subst k
    by_contra hne
    have hl : l ≠ 0 := Ne.symm hne
    have hv := congrArg (fun v : Vertex => v.1 l) h
    simp [p4Q2PZ37ADO_fourSpatialVertices, hl] at hv
    exact hOne hv.symm
  · by_contra hne
    have hv := congrArg (fun v : Vertex => v.1 k) h
    simp [p4Q2PZ37ADO_fourSpatialVertices, hk, hne, hOne] at hv

/-- The original spatial time-zero link carrier has at least twelve
ACTUAL edges: four distinct base vertices × three spatial axes.
No assumed physical link-count lower bound is introduced. -/
theorem p4Q2PZ37ADO_originalSpatialLinkCount_ge_twelve :
    12 ≤ Fintype.card Link := by
  have hVertex : 4 ≤ Fintype.card Vertex := by
    simpa using
      (Fintype.card_le_of_injective
        (p4Q2PZ37ADO_fourSpatialVertices H)
        (p4Q2PZ37ADO_fourSpatialVertices_injective H))
  have hDirection : Fintype.card Direction = 3 := by decide
  have hCard : Fintype.card Link =
      Fintype.card Vertex * Fintype.card Direction := by
    calc
      Fintype.card Link = Nat.card Link :=
        (Nat.card_eq_fintype_card).symm
      _ = Nat.card Vertex * Nat.card Direction :=
        Nat.card_prod Vertex Direction
      _ = Fintype.card Vertex * Fintype.card Direction := by
        simp only [Nat.card_eq_fintype_card]
  rw [hCard, hDirection]
  omega

/-- The ORIGINAL full all-link D_H Haar ball obeys a strictly
radius-dependent explicit upper bound using the genuine ADK cap. -/
theorem p4Q2PZ37ADO_originalFullBall_mass_le_sevenEighthPower
    (a : Pair) (R : ℝ) (hR : 0 < R)
    (hSq : R ^ 2 ≤ (39 / 16 : ℝ)) :
    Measure.real outer (Ball a R) ≤
      (7 / 8 : ℝ) ^ (2 * Fintype.card Link) := by
  have hm := p4Q2PZ37ADO_radialMass_le_sevenEighths R hR hSq
  exact
    (p4Q2PZ37ADN_originalFullBall_mass_le_radialPower H a R).trans
      (pow_le_pow_left₀ (measureReal_nonneg) hm _)

/-- The new explicitly calibrated genuine full ball mass is
universally at most (7/8)^24, and this is STRICTLY below 1/17.
This strengthens ADN past the √2 radius threshold. -/
theorem p4Q2PZ37ADO_originalFullBall_mass_lt_oneSeventeenth
    (a : Pair) (R : ℝ) (hR : 0 < R)
    (hSq : R ^ 2 ≤ (39 / 16 : ℝ)) :
    Measure.real outer (Ball a R) < (1 / 17 : ℝ) := by
  have hMass :=
    p4Q2PZ37ADO_originalFullBall_mass_le_sevenEighthPower
      H a R hR hSq
  have hCard :=
    p4Q2PZ37ADO_originalSpatialLinkCount_ge_twelve H
  have hExponent : 24 ≤ 2 * Fintype.card Link := by omega
  have hPower :
      (7 / 8 : ℝ) ^ (2 * Fintype.card Link) ≤
        (7 / 8 : ℝ) ^ 24 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hExponent
  have hNumeric : (7 / 8 : ℝ) ^ 24 < 1 / 17 := by norm_num
  exact hMass.trans_lt (hPower.trans_lt hNumeric)

/-- The original fixed radius R=3/2 is now certified small enough
for the SAME original all-link Haar mass to stay below 1/17. -/
theorem p4Q2PZ37ADO_originalFullBall_threeHalves_mass_lt_oneSeventeenth
    (a : Pair) :
    Measure.real outer (Ball a (3 / 2)) < (1 / 17 : ℝ) :=
  p4Q2PZ37ADO_originalFullBall_mass_lt_oneSeventeenth
    H a (3 / 2) (by norm_num) (by norm_num)

/-- The ADI 68-condition is numerically obstructed throughout
the extended genuine physical D_H ball regime 0<R and R²≤39/16.
The exact original covariance and K_H are used, without
an invented global physical Lipschitz coefficient. -/
theorem p4Q2PZ37ADO_originalExtendedFullBall_obstructs_68Certificate
    (e : Link) (a : Pair) (R : ℝ)
    (hR : 0 < R) (hSq : R ^ 2 ≤ (39 / 16 : ℝ)) :
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) ^ 2 *
      Measure.real outer (Ball a R) ≤ K := by
  apply p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric
    H e a (Ball a R)
  exact (p4Q2PZ37ADO_originalFullBall_mass_lt_oneSeventeenth
    H a R hR hSq).le

/-- The new explicit three-halves radius cannot satisfy the
strict ADH numeric sufficient condition for the original source
and receiver, at ANY finite H, link e, or physical boundary a. -/
theorem p4Q2PZ37ADO_originalThreeHalvesBall_obstructs_68Certificate
    (e : Link) (a : Pair) :
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) ^ 2 *
      Measure.real outer (Ball a (3 / 2)) ≤ K :=
  p4Q2PZ37ADO_originalExtendedFullBall_obstructs_68Certificate
    H e a (3 / 2) (by norm_num) (by norm_num)

/-- At each fixed genuine subdiameter radius R<2, the original
all-link ball has Haar mass strictly less than one for every H,
even where no explicit absolute fraction is known. -/
theorem p4Q2PZ37ADO_originalFullBall_mass_lt_one_below_two
    (a : Pair) (R : ℝ) (hR : 0 < R) (hRtwo : R < 2) :
    Measure.real outer (Ball a R) < 1 := by
  have hm := p4Q2PZ37ADO_radialMass_lt_one_below_two R hR hRtwo
  have hmNonneg : 0 ≤ m R := measureReal_nonneg
  have hmLe : m R ≤ 1 := hm.le
  have hCard := p4Q2PZ37ADO_originalSpatialLinkCount_ge_twelve H
  have hExponent : 1 ≤ 2 * Fintype.card Link := by omega
  have hPower : m R ^ (2 * Fintype.card Link) ≤ m R := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one hmNonneg hmLe hExponent)
  exact (p4Q2PZ37ADN_originalFullBall_mass_le_radialPower
    H a R).trans_lt (hPower.trans_lt hm)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_twoAntipodalChordSquares_eq_four
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_twoRadiusAntipodalBalls_disjoint
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_twoRadiusHaarMass_sum_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_radialMass_lt_one_below_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_radialMass_le_sevenEighths
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADO_radialMass_threeHalves_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_fourSpatialVertices_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalSpatialLinkCount_ge_twelve
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalFullBall_mass_le_sevenEighthPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalFullBall_mass_lt_oneSeventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalFullBall_threeHalves_mass_lt_oneSeventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalExtendedFullBall_obstructs_68Certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalThreeHalvesBall_obstructs_68Certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADO_originalFullBall_mass_lt_one_below_two
