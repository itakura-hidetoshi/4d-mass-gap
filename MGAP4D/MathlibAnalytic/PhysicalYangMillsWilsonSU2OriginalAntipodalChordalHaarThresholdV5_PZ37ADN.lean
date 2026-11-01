import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullChordalCovarianceModulusV5_PZ37ADM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADN — original antipodal SU(2) chordal-Haar thresholds

The SAME original normalized SU(2) compact Haar, the ADK genuine eight-real
matrix feature J, ADM radial Haar mass m(r), and the original pair-Haar
all-link chordal metric are retained without changing the physical model.

The existing genuine central element z = -1 of SU(2) acts by E(z*g)=2-E(g).
Therefore the two true radius-r balls at 1 and z are disjoint if r² ≤ 2,
and together cover SU(2) if 2 < r² (r positive).
Their genuine Haar masses coincide by ADM translation invariance.

It follows that m(r) ≤ 1/2 for 0<r and r²≤2, while m(r) ≥ 1/2
for r>0 and r²>2. At r=3/2 this improves ADK's old 1/8 bound to 1/2.
This is an actual radius-dependent numerical bound, but does NOT provide
a lower bound for arbitrarily small positive r.

Every original all-link D_H-ball lies in its coordinatewise radius-r box.
Thus its pair-Haar mass is at most m(r)^(2*card(Link_H)).
The original spatial slice has at least three physical links; at
0<r and r²≤2 the bound is ≤1/64 <1/17. Consequently ADI's
actual original K_H/68 numerical sufficient certificate cannot hold
on any such D_H-ball, regardless of the nonzero covariance witness.

The obstruction concerns this exact single-ball sufficient criterion,
not a physical absence of signed response or a continuum mass gap.
No unverified Lipschitz constant, covariance amplitude, or small-r
lower Haar mass is introduced.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local instance p4Q2PZ37ADN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADN_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Exact ORIGINAL chordal energy at the identity. -/
theorem p4Q2PZ37ADN_identityChordal_sq (g : G) :
    dJ (1 : G) g ^ 2 = 2 * E g := by
  simpa using
    (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (1 : G) g)

/-- Exact ORIGINAL chordal energy at the central antipode. -/
theorem p4Q2PZ37ADN_antipodalChordal_sq (g : G) :
    dJ z g ^ 2 = 2 * (2 - E g) := by
  rw [p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy,
    p4Q2PZ37ABV_centralMinusOne_inv,
    p4Q2PZ37ABV_central_mul_energy]

/-- Original SU(2) antipodal open balls are disjoint at 0<r and r²≤2. -/
theorem p4Q2PZ37ADN_antipodalBalls_disjoint
    (r : ℝ) (hr : 0 < r) (hSq : r ^ 2 ≤ 2) :
    Disjoint (BallJ (1 : G) r) (BallJ z r) := by
  apply Set.disjoint_left.mpr
  intro g hgOne hgAnt
  have hOne : dJ (1 : G) g < r := hgOne
  have hAnt : dJ z g < r := hgAnt
  have hOneNN : 0 ≤ dJ (1 : G) g :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  have hAntNN : 0 ≤ dJ z g :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  have hOneSq : dJ (1 : G) g ^ 2 < r ^ 2 := by
    have hProd : 0 < (r - dJ (1 : G) g) * (r + dJ (1 : G) g) :=
      mul_pos (sub_pos.mpr hOne) (add_pos_of_pos_of_nonneg hr hOneNN)
    nlinarith
  have hAntSq : dJ z g ^ 2 < r ^ 2 := by
    have hProd : 0 < (r - dJ z g) * (r + dJ z g) :=
      mul_pos (sub_pos.mpr hAnt) (add_pos_of_pos_of_nonneg hr hAntNN)
    nlinarith
  have hEnergyOne := p4Q2PZ37ADN_identityChordal_sq g
  have hEnergyAnt := p4Q2PZ37ADN_antipodalChordal_sq g
  linarith

/-- The true ORIGINAL normalized SU(2) radial ball has at most
one half of Haar for r²≤2. -/
theorem p4Q2PZ37ADN_radialMass_le_half
    (r : ℝ) (hr : 0 < r) (hSq : r ^ 2 ≤ 2) :
    m r ≤ (1 / 2 : ℝ) := by
  have hDisjoint := p4Q2PZ37ADN_antipodalBalls_disjoint r hr hSq
  have hSub : BallJ z r ⊆ (BallJ (1 : G) r)ᶜ := by
    intro g hg hs
    exact (Set.disjoint_left.mp hDisjoint) hs hg
  have hAntMass : Measure.real haar (BallJ z r) = m r :=
    p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial z r
  have hOther : m r ≤ Measure.real haar (BallJ (1 : G) r)ᶜ := by
    rw [← hAntMass]
    exact measureReal_mono hSub
  have hCompl :=
    measureReal_add_measureReal_compl (μ := haar)
      (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) r).measurableSet
  have hUniv : Measure.real haar Set.univ = 1 := by simp
  rw [hUniv] at hCompl
  change m r + Measure.real haar (BallJ (1 : G) r)ᶜ = 1 at hCompl
  linarith

/-- Above the exact antipodal threshold the two genuine Haar
ball translates cover the WHOLE original SU(2) group. -/
theorem p4Q2PZ37ADN_antipodalBalls_cover
    (r : ℝ) (hr : 0 < r) (hSq : 2 < r ^ 2) :
    BallJ (1 : G) r ∪ BallJ z r = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro g
  by_cases hOne : dJ (1 : G) g < r
  · exact Or.inl hOne
  · right
    have hGe : r ≤ dJ (1 : G) g := le_of_not_gt hOne
    have hOneNN : 0 ≤ dJ (1 : G) g :=
      p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
    have hAntNN : 0 ≤ dJ z g :=
      p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
    have hSqGe : r ^ 2 ≤ dJ (1 : G) g ^ 2 := by
      have hProd : 0 ≤
          (dJ (1 : G) g - r) * (dJ (1 : G) g + r) :=
        mul_nonneg (sub_nonneg.mpr hGe)
          (add_nonneg hOneNN hr.le)
      nlinarith
    have hIdentity := p4Q2PZ37ADN_identityChordal_sq g
    have hAntipode := p4Q2PZ37ADN_antipodalChordal_sq g
    have hSmallSq : dJ z g ^ 2 < r ^ 2 := by
      linarith
    have hSmall : dJ z g < r := by
      nlinarith
    exact hSmall

/-- The original Haar radial mass is at least one half whenever
r>0 and r²>2; no measure surrogate or coordinate distribution
is used. -/
theorem p4Q2PZ37ADN_radialMass_ge_half
    (r : ℝ) (hr : 0 < r) (hSq : 2 < r ^ 2) :
    (1 / 2 : ℝ) ≤ m r := by
  have hCover := p4Q2PZ37ADN_antipodalBalls_cover r hr hSq
  have hSub : (BallJ (1 : G) r)ᶜ ⊆ BallJ z r := by
    intro g hg
    have hmem : g ∈ BallJ (1 : G) r ∪ BallJ z r := by
      rw [hCover]
      trivial
    exact hmem.resolve_left hg
  have hAntMass : Measure.real haar (BallJ z r) = m r :=
    p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial z r
  have hOther : Measure.real haar (BallJ (1 : G) r)ᶜ ≤ m r := by
    rw [← hAntMass]
    exact measureReal_mono hSub
  have hCompl :=
    measureReal_add_measureReal_compl (μ := haar)
      (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) r).measurableSet
  have hUniv : Measure.real haar Set.univ = 1 := by simp
  rw [hUniv] at hCompl
  change m r + Measure.real haar (BallJ (1 : G) r)ᶜ = 1 at hCompl
  linarith

/-- A concrete improved numeric bound at original chordal radius 3/2. -/
theorem p4Q2PZ37ADN_radiusThreeHalves_mass_ge_half :
    (1 / 2 : ℝ) ≤ m (3 / 2) :=
  p4Q2PZ37ADN_radialMass_ge_half (3 / 2) (by norm_num) (by norm_num)

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Box" => p4Q2PZ37ADL_originalFullBoundaryChordalBox H
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "K" => p4Q2PZ37ADF_originalTransferPlaquetteFCBound H
local instance p4Q2PZ37ADN_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADN_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Every genuine original D_H ball is contained in the ORIGINAL
coordinatewise box at the SAME radius, by nonnegativity of each
single-link contribution to D_H. -/
theorem p4Q2PZ37ADN_originalFullBall_subset_sameRadiusBox
    (a : Pair) (R : ℝ) :
    Ball a R ⊆ Box a R := by
  intro w hw
  have hSum : D a w < R := hw
  have hTerm (e : Link) :
      dJ (a.1 e) (w.1 e) + dJ (a.2 e) (w.2 e) ≤ D a w := by
    unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
    exact Finset.single_le_sum (fun i _ =>
      add_nonneg
        (p4Q2PZ37ADK_trueChordalDistance_nonneg (a.1 i) (w.1 i))
        (p4Q2PZ37ADK_trueChordalDistance_nonneg (a.2 i) (w.2 i)))
      (Finset.mem_univ e)
  constructor
  · intro e _he
    exact lt_of_le_of_lt
      (le_trans
        (le_add_of_nonneg_right
          (p4Q2PZ37ADK_trueChordalDistance_nonneg (a.2 e) (w.2 e)))
        (hTerm e)) hSum
  · intro e _he
    exact lt_of_le_of_lt
      (le_trans
        (le_add_of_nonneg_left
          (p4Q2PZ37ADK_trueChordalDistance_nonneg (a.1 e) (w.1 e)))
        (hTerm e)) hSum

/-- Exact original full-box Haar probability yields a valid
radius-dependent UPPER bound for the same original D_H ball. -/
theorem p4Q2PZ37ADN_originalFullBall_mass_le_radialPower
    (a : Pair) (R : ℝ) :
    Measure.real outer (Ball a R) ≤
      m R ^ (2 * Fintype.card Link) := by
  calc
    Measure.real outer (Ball a R) ≤
        Measure.real outer (Box a R) :=
      measureReal_mono (p4Q2PZ37ADN_originalFullBall_subset_sameRadiusBox H a R)
    _ = m R ^ (2 * Fintype.card Link) :=
      p4Q2PZ37ADM_originalFullBoxHaarMass_exactRadialPower H a R

/-- For r²≤2, the TRUE original all-link ball probability is
numerically bounded by the two-boundary link count. -/
theorem p4Q2PZ37ADN_originalFullBall_mass_le_halfPower
    (a : Pair) (R : ℝ) (hR : 0 < R) (hSq : R ^ 2 ≤ 2) :
    Measure.real outer (Ball a R) ≤
      (1 / 2 : ℝ) ^ (2 * Fintype.card Link) := by
  exact (p4Q2PZ37ADN_originalFullBall_mass_le_radialPower H a R).trans
    (pow_le_pow_left₀
      (by exact measureReal_nonneg)
      (p4Q2PZ37ADN_radialMass_le_half R hR hSq)
      (2 * Fintype.card Link))

/-- The genuine finite spatial slice has at least three links:
one zero-time lattice vertex times the three spatial directions.
This is a theorem about the ORIGINAL geometry, not an assumption. -/
theorem p4Q2PZ37ADN_originalSpatialLinkCount_ge_three :
    3 ≤ Fintype.card Link := by
  letI : Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
  have hVertex : Nonempty (PeriodicHypercubicEvenSpatialSliceVertex H) := by
    refine ⟨⟨fun _ => 0, ?_⟩⟩
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]
  have hPositive :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) :=
    Fintype.card_pos_iff.mpr hVertex
  have hDirection :
      Fintype.card PeriodicHypercubicEvenSpatialDirection = 3 := by
    decide
  have hCard : Fintype.card Link =
      Fintype.card (PeriodicHypercubicEvenSpatialSliceVertex H) *
        Fintype.card PeriodicHypercubicEvenSpatialDirection := by
    exact Fintype.card_prod _ _
  rw [hCard, hDirection]
  omega

/-- Every genuine small original full-link D_H ball has pair-Haar
mass at most 1/64 (not merely positive). -/
theorem p4Q2PZ37ADN_originalSmallFullBall_mass_le_sixtyFour
    (a : Pair) (R : ℝ) (hR : 0 < R) (hSq : R ^ 2 ≤ 2) :
    Measure.real outer (Ball a R) ≤ (1 / 64 : ℝ) := by
  have hPower :=
    p4Q2PZ37ADN_originalFullBall_mass_le_halfPower H a R hR hSq
  have hCard := p4Q2PZ37ADN_originalSpatialLinkCount_ge_three H
  have hSix : 6 ≤ 2 * Fintype.card Link := by omega
  have hPowerBound :
      (1 / 2 : ℝ) ^ (2 * Fintype.card Link) ≤ (1 / 2 : ℝ) ^ 6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hSix
  have hNumeric : (1 / 2 : ℝ) ^ 6 = 1 / 64 := by norm_num
  linarith

/-- This EXACT original metric-ball radius regime fails the
ADI necessary >1/17 mass test, for every finite H and actual
physical boundary center. -/
theorem p4Q2PZ37ADN_originalSmallFullBall_mass_lt_oneSeventeenth
    (a : Pair) (R : ℝ) (hR : 0 < R) (hSq : R ^ 2 ≤ 2) :
    Measure.real outer (Ball a R) < (1 / 17 : ℝ) := by
  have hMass :=
    p4Q2PZ37ADN_originalSmallFullBall_mass_le_sixtyFour
      H a R hR hSq
  linarith

/-- Numeric obstruction for the existing original centered physical
covariance and original transfer/plaquette cap on every D_H ball
in the small-radius regime; the coefficient 68 is unchanged. -/
theorem p4Q2PZ37ADN_originalSmallFullBall_obstructs_68Certificate
    (e : Link) (a : Pair) (R : ℝ)
    (hR : 0 < R) (hSq : R ^ 2 ≤ 2) :
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) ^ 2 *
        Measure.real outer (Ball a R) ≤ K := by
  apply p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric
    H e a (Ball a R)
  exact (p4Q2PZ37ADN_originalSmallFullBall_mass_lt_oneSeventeenth
    H a R hR hSq).le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_identityChordal_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_antipodalChordal_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_antipodalBalls_disjoint
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_radialMass_le_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_antipodalBalls_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_radialMass_ge_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADN_radiusThreeHalves_mass_ge_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalFullBall_subset_sameRadiusBox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalFullBall_mass_le_radialPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalFullBall_mass_le_halfPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalSpatialLinkCount_ge_three
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalSmallFullBall_mass_le_sixtyFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalSmallFullBall_mass_lt_oneSeventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADN_originalSmallFullBall_obstructs_68Certificate
