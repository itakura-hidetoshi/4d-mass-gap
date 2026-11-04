import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAntipodalTwoCellEffectiveHaarV5_PZ37AFO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFP — eight explicit genuine quaternion chordal cells

AFO constructed a literal two-cell true SU(2) Haar certificate at
radius 3/2. The original ABV eight QUATERNION low-energy-cap cover,
combined with the original ADK Wilson energy/chordal calibration,
gives a much sharper finite set of ACTUAL SU(2) centers.

At each original group element g, ABV supplies one of eight genuine
quaternion translations a such that E(a*g) <= 1/2. Hence
  d_J(a^-1,g)^2 = 2 E(a*g) <= 1,
so the eight EXPLICIT inverse-quaternion centers form a closed
chordal 1-net, and an OPEN ball cover for every radius r > 1.
No noncomputable compactness net, substitute group, or invented
probability measure is involved.

AFN's first-covering-center construction yields exactly eight
indexed genuine Borel cells with center radius r.
For 1 < r and r^2 <= 2, ADN's authentic antipodal ball upper mass
gives 0 <= Haar(C_i) <= 1/2 for each cell. The explicit, positive
rational weight 1/8 for each of the eight cells, with certified
error 3/8, sums to one. These mass intervals are coarse; the
eight cells are not proved Haar-equiprobable.

At the literal rational radius 9/8, the SAME original signed FF
physical receiver F, its square, and its four genuine Haar mode
products are given explicit rational ZERO samples. Their true
errors are bounded by the unchanged physical FF BCF norm M_FF
(and its square), exactly as established in AFO.

This produces the AFM->AFL->AFK->AFJ->AFI typed certificate
from eight original matrix centers, with no inferred positive
threshold crossing, numerical narrow samples, uniform coercivity,
Hamiltonian gap, or continuum Yang--Mills mass gap.
The original Wilson source, Perron transfer, true Haar, FC budget,
public roots and pinned Lean/mathlib are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "cap" => p4Q2PZ37ABV_capTranslate

local instance p4Q2PZ37AFP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFP_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Explicit eight ORIGINAL SU(2) group elements. The source is
the already-proved genuine ABV quaternion family with both
central signs; only group inversion is applied to each element. -/
noncomputable def p4Q2PZ37AFP_eightCenters : Fin 8 → G :=
  ![(cap (0, false))⁻¹, (cap (1, false))⁻¹,
    (cap (2, false))⁻¹, (cap (3, false))⁻¹,
    (cap (0, true))⁻¹, (cap (1, true))⁻¹,
    (cap (2, true))⁻¹, (cap (3, true))⁻¹]

/-- Each of the eight ACTUAL ABV quaternion cap translations
occurs in the explicit Fin8 centers, with no chosen compact net. -/
theorem p4Q2PZ37AFP_eightCenters_enumerates
    (i : Fin 4 × Bool) :
    ∃ k : Fin 8, p4Q2PZ37AFP_eightCenters k = (cap i)⁻¹ := by
  rcases i with ⟨j, s⟩
  cases s with
  | false =>
    fin_cases j
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  | true =>
    fin_cases j
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩

/-- The old genuine ABV low-energy cap, transported through the
old ADK EXACT squared chord, proves a closed radius-ONE net.
The bound is literal 1, not a compactness existence parameter. -/
theorem p4Q2PZ37AFP_eightCenters_unitChordCover
    (g : G) :
    ∃ k : Fin 8, dJ (p4Q2PZ37AFP_eightCenters k) g ≤ 1 := by
  have hCapCover :
      g ∈ ⋃ i : Fin 4 × Bool,
        (fun u : G => cap i * u) ⁻¹'
          p4Q2PZ37ABV_lowEnergyCap := by
    rw [p4Q2PZ37ABV_eight_cap_cover]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hCapCover
  have hEnergy : E (cap i * g) ≤ (1 / 2 : ℝ) := hi
  obtain ⟨k, hk⟩ := p4Q2PZ37AFP_eightCenters_enumerates i
  refine ⟨k, ?_⟩
  rw [hk]
  have hSq :
      (dJ (cap i)⁻¹ g) ^ 2 = 2 * E (cap i * g) := by
    simpa only [inv_inv] using
      (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (cap i)⁻¹ g)
  have hNN : 0 ≤ dJ (cap i)⁻¹ g :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  nlinarith only [hSq, hEnergy, hNN]

/-- The eight specified original SU(2) quaternion elements form
a genuine OPEN ball cover at EVERY numeric radius strictly above 1.
This is stronger in radius than AFO's two centers of radius 3/2. -/
theorem p4Q2PZ37AFP_eightCenters_ballCover
    (r : ℝ) (hr : 1 < r) :
    ∀ g : G, ∃ k : Fin 8,
      g ∈ BallJ (p4Q2PZ37AFP_eightCenters k) r := by
  intro g
  obtain ⟨k, hk⟩ := p4Q2PZ37AFP_eightCenters_unitChordCover g
  exact ⟨k, lt_of_le_of_lt hk hr⟩

/-- The genuine eight-cell first-center tie break from AFN:
it uses the SAME original d_J, not discrete counting Haar. -/
def p4Q2PZ37AFP_eightCells
    (r : ℝ) (i : Fin 8) : Set G :=
  p4Q2PZ37AFN_originalFirstCenterCell
    8 p4Q2PZ37AFP_eightCenters r i

theorem p4Q2PZ37AFP_eightCells_measurable
    (r : ℝ) (i : Fin 8) :
    MeasurableSet (p4Q2PZ37AFP_eightCells r i) :=
  p4Q2PZ37AFN_originalFirstCenterCell_measurable
    8 p4Q2PZ37AFP_eightCenters r i

theorem p4Q2PZ37AFP_eightCells_partition
    (r : ℝ) (hr : 1 < r) :
    ∀ g : G, ∃ i : Fin 8,
      g ∈ p4Q2PZ37AFP_eightCells r i ∧
      ∀ j : Fin 8, g ∈ p4Q2PZ37AFP_eightCells r j → j = i :=
  p4Q2PZ37AFN_originalFirstCenterCell_partition
    8 p4Q2PZ37AFP_eightCenters r
    (p4Q2PZ37AFP_eightCenters_ballCover r hr)

/-- Each genuine first-center Borel cell lies in its original
specified quaternion-centered radius-r chordal ball. -/
theorem p4Q2PZ37AFP_eightCells_chordalRadius
    (r : ℝ) (i : Fin 8) (g : G)
    (hg : g ∈ p4Q2PZ37AFP_eightCells r i) :
    dJ g (p4Q2PZ37AFP_eightCenters i) ≤ r := by
  have hBall : g ∈ BallJ (p4Q2PZ37AFP_eightCenters i) r :=
    (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      8 p4Q2PZ37AFP_eightCenters r i g).1 hg |>.1
  calc
    dJ g (p4Q2PZ37AFP_eightCenters i) =
        dJ (p4Q2PZ37AFP_eightCenters i) g :=
      p4Q2PZ37ADK_trueChordalDistance_symm _ _
    _ ≤ r := le_of_lt hBall

/-- If r²<=2, ADN's original antipodal Haar theorem bounds
EACH of the actual eight Borel cell masses from above by 1/2.
The bound is coarse, but needs no guessed cell distribution. -/
theorem p4Q2PZ37AFP_eightCells_trueHaar_mass_le_half
    (r : ℝ) (hr : 1 < r) (hrSq : r ^ 2 ≤ 2) (i : Fin 8) :
    Measure.real mu (p4Q2PZ37AFP_eightCells r i) ≤ (1 / 2 : ℝ) := by
  have hSubset :
      p4Q2PZ37AFP_eightCells r i ⊆
        BallJ (p4Q2PZ37AFP_eightCenters i) r := by
    intro g hg
    exact (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      8 p4Q2PZ37AFP_eightCenters r i g).1 hg |>.1
  calc
    Measure.real mu (p4Q2PZ37AFP_eightCells r i) ≤
        Measure.real mu (BallJ (p4Q2PZ37AFP_eightCenters i) r) :=
      measureReal_mono hSubset (measure_ne_top _ _)
    _ = p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass r :=
      p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial _ r
    _ ≤ 1 / 2 :=
      p4Q2PZ37ADN_radialMass_le_half r
        (lt_trans (by norm_num : (0 : ℝ) < 1) hr) hrSq

/-- The eight literal rational weights are all 1/8 and add up
to exactly one, even though equiprobability of TRUE cells is
NOT asserted. -/
def p4Q2PZ37AFP_eightRationalWeight (_i : Fin 8) : ℚ :=
  1 / 8

theorem p4Q2PZ37AFP_eightRationalWeight_sum_one :
    (∑ i : Fin 8, p4Q2PZ37AFP_eightRationalWeight i) = 1 := by
  norm_num [p4Q2PZ37AFP_eightRationalWeight]

theorem p4Q2PZ37AFP_eightRationalWeight_positive (i : Fin 8) :
    0 < p4Q2PZ37AFP_eightRationalWeight i := by
  norm_num [p4Q2PZ37AFP_eightRationalWeight]

/-- TRUE Haar-cell mass errors are bounded by the fully explicit
3/8 tolerance using only 0<=mu(C_i)<=1/2, not unproved symmetry.
The numerical error is broader than AFO's 3/16. -/
theorem p4Q2PZ37AFP_eightHaarRational_accuracy
    (r : ℝ) (hr : 1 < r) (hrSq : r ^ 2 ≤ 2) (i : Fin 8) :
    |Measure.real mu (p4Q2PZ37AFP_eightCells r i) -
      (p4Q2PZ37AFP_eightRationalWeight i : ℝ)| ≤ (3 / 8 : ℝ) := by
  have h0 : 0 ≤ Measure.real mu (p4Q2PZ37AFP_eightCells r i) :=
    measureReal_nonneg
  have h1 :=
    p4Q2PZ37AFP_eightCells_trueHaar_mass_le_half r hr hrSq i
  change |Measure.real mu (p4Q2PZ37AFP_eightCells r i) -
    (1 / 8 : ℝ)| ≤ (3 / 8 : ℝ)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- ORIGINAL AFJ normalized Haar structure with eight concrete
quaternion centers, genuine AFN cells and fixed rational weights.
No real-weight choice oracle or substitute finite Haar. -/
def p4Q2PZ37AFP_originalEightHaarCells
    (r : ℝ) (hr : 1 < r) (hrSq : r ^ 2 ≤ 2) :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := 8
  cell := p4Q2PZ37AFP_eightCells r
  hMeas := p4Q2PZ37AFP_eightCells_measurable r
  hPartition := p4Q2PZ37AFP_eightCells_partition r hr
  weight := p4Q2PZ37AFP_eightRationalWeight
  weightError := fun _ => (3 / 8 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy :=
    p4Q2PZ37AFP_eightHaarRational_accuracy r hr hrSq

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0
local notation "MFF" => p4Q2PZ37AFM_originalFFEnvelope H
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter

local instance p4Q2PZ37AFP_links : Fintype Link := Fintype.ofFinite _

/-- The original signed Wilson/Perron FF receiver on EIGHT true
SU(2) quaternion centers, with literal rational ZERO samples and
honest original physical BCF-norm error bounds. The explicit radius
is 9/8 < AFO's 3/2, with no numerical sample-value oracle. -/
def p4Q2PZ37AFP_explicitPhysicalEightCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c where
  partition := p4Q2PZ37AFP_originalEightHaarCells
    (9 / 8) (by norm_num) (by norm_num)
  center := p4Q2PZ37AFP_eightCenters
  radius := 9 / 8
  hRadius := by norm_num
  hCellRadius := by
    intro i g hg
    exact p4Q2PZ37AFP_eightCells_chordalRadius (9 / 8) i g hg
  hThetaLo := hlo
  meanSample := fun _ _ => 0
  meanSampleError := fun _ => MFF e
  hMeanSampleError_nonneg := by
    intro a ha
    exact p4Q2PZ37AFM_originalFFEnvelope_nonneg H e
  hMeanSample := by
    intro a ha i
    simpa only [Rat.cast_zero, sub_zero] using
      (p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm
        H e a (p4Q2PZ37AFP_eightCenters i))
  secondSample := fun _ _ => 0
  secondSampleError := fun _ => (MFF e) ^ 2
  hSecondSampleError_nonneg := by
    intro a ha
    exact sq_nonneg _
  hSecondSample := by
    intro a ha i
    have hBound := p4Q2PZ37AFO_originalFF_square_le_normSquare
      H e a (p4Q2PZ37AFP_eightCenters i)
    have hSq : 0 ≤ (F e a (p4Q2PZ37AFP_eightCenters i)) ^ 2 :=
      sq_nonneg _
    simpa only [Rat.cast_zero, sub_zero, abs_of_nonneg hSq] using hBound
  coefficientSample := fun _ _ _ => 0
  coefficientSampleError := fun _ _ => MFF e
  hCoefficientSampleError_nonneg := by
    intro a ha j
    exact p4Q2PZ37AFM_originalFFEnvelope_nonneg H e
  hCoefficientSample := by
    intro a ha j i
    simpa only [Rat.cast_zero, sub_zero] using
      (p4Q2PZ37AFO_originalFF_character_abs_le_norm
        H e a j (p4Q2PZ37AFP_eightCenters i))

/-- The same unchanged AFM certificate is instantiated by this
precise 9/8 radius and eight fixed original SU(2) group centers. -/
theorem p4Q2PZ37AFP_originalEightCell_certificate_radius
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    (p4Q2PZ37AFP_explicitPhysicalEightCellSamples H e c hlo).radius =
      (9 / 8 : ℝ) := rfl

/-- The existing original Wilson/Perron coefficient/variance Haar
certificate, retaining AFG's real independent table c and its
strict physical shell inequalities as separate future obligations. -/
def p4Q2PZ37AFP_explicitTrueCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    H e c (p4Q2PZ37AFP_explicitPhysicalEightCellSamples H e c hlo)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCenters_enumerates
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCenters_unitChordCover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCenters_ballCover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCells_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCells_partition
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCells_chordalRadius
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightCells_trueHaar_mass_le_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightRationalWeight_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightRationalWeight_positive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFP_eightHaarRational_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFP_originalEightCell_certificate_radius
