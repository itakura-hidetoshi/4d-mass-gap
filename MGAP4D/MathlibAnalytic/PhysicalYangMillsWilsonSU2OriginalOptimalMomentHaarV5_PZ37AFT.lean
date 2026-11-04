import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2Original24CellMomentMarkovHaarV5_PZ37AFS
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFT — optimal second-moment Markov shift and physical quadrature

The AFS original SU(2) Haar character has E[chi]=0 and E[chi^2]=1/4.
On the genuine radius-4/5 J-chordal ball, chi > 17/25. Optimizing
E[(chi+c)^2]/(17/25+c)^2 over c > -17/25 gives c=25/68. The integer
polynomial (68 chi+25)^2 has exact Haar expectation 1781, and is
at least 3171961/625 on that ball. The verified Haar upper bound is

  m(4/5) <= 625/1781 < 1250/3481.

On the SAME twenty-four first-center Borel cells as AFQ/AFR/AFS:
  1/160000 <= Haar(cell i) <= 625/1781,
  |Haar(cell i)-1/24| <= 13219/42744.

The new fixed-rational AFJ quadrature is connected directly to the
unchanged physical AFM -> AFL -> AFK -> AFJ -> AFI construction.
Only genuinely certified rational receiver samples are admitted.
A numerical shell crossing or uniform physical spectral gap is NOT
asserted. The zero-sample fallback itself cannot benefit from the
smaller weight error, because its sample-weight terms vanish.
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
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters

local instance p4Q2PZ37AFT_topological : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFT_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFT_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFT_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFT_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFT_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The exactly minimizing rational shift within the Markov-square family. -/
theorem p4Q2PZ37AFT_rationalShift_optimal (c : ℝ)
    (hc : 0 < c + 17 / 25) :
    (625 / 1781 : ℝ) ≤ (c ^ 2 + 1 / 4) / (c + 17 / 25) ^ 2 := by
  have hp : 0 < (c + 17 / 25) ^ 2 := pow_pos hc 2
  apply (le_div_iff₀ hp).2
  nlinarith only [sq_nonneg ((17 / 25 : ℝ) * c - 1 / 4)]

theorem p4Q2PZ37AFT_rationalShift_attains_optimum :
    (((25 / 68 : ℝ) ^ 2 + 1 / 4) /
      ((25 / 68 : ℝ) + 17 / 25) ^ 2) = 625 / 1781 := by
  norm_num

/-- An integer-coefficient square of the original physical Wilson character. -/
def p4Q2PZ37AFT_optimalMarkovSquare (g : G) : ℝ :=
  (68 * chi g + 25) ^ 2

/-- Reuse AFS's proven shifted-square moment and original character mean. -/
theorem p4Q2PZ37AFT_optimalMarkovSquare_linearAFS (g : G) :
    p4Q2PZ37AFT_optimalMarkovSquare g =
      4624 * p4Q2PZ37AFS_shiftedSquare g - 1224 * chi g - 531 := by
  unfold p4Q2PZ37AFT_optimalMarkovSquare p4Q2PZ37AFS_shiftedSquare
  ring

theorem p4Q2PZ37AFT_optimalMarkovSquare_nonneg (g : G) :
    0 ≤ p4Q2PZ37AFT_optimalMarkovSquare g := by
  unfold p4Q2PZ37AFT_optimalMarkovSquare
  exact sq_nonneg _

theorem p4Q2PZ37AFT_optimalMarkovSquare_integrable :
    Integrable p4Q2PZ37AFT_optimalMarkovSquare mu := by
  have hc : Continuous chi :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hQ : Continuous p4Q2PZ37AFT_optimalMarkovSquare := by
    unfold p4Q2PZ37AFT_optimalMarkovSquare
    exact ((continuous_const.mul hc).add continuous_const).pow 2
  exact hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Actual normalized SU(2) Haar expectation, not a proxy sphere moment. -/
theorem p4Q2PZ37AFT_optimalMarkovSquare_integral :
    (∫ g : G, p4Q2PZ37AFT_optimalMarkovSquare g ∂mu) = (1781 : ℝ) := by
  have hc : Continuous chi :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hIntChi : Integrable chi mu :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntA := p4Q2PZ37AFS_shiftedSquare_integrable
  have hIntL :
      Integrable (fun g : G =>
        (4624 : ℝ) * p4Q2PZ37AFS_shiftedSquare g - 1224 * chi g) mu :=
    (hIntA.const_mul _).sub (hIntChi.const_mul _)
  calc
    (∫ g : G, p4Q2PZ37AFT_optimalMarkovSquare g ∂mu) =
        (∫ g : G, ((4624 : ℝ) * p4Q2PZ37AFS_shiftedSquare g -
          1224 * chi g) - 531 ∂mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall p4Q2PZ37AFT_optimalMarkovSquare_linearAFS
    _ = 4624 * (∫ g : G, p4Q2PZ37AFS_shiftedSquare g ∂mu) -
          1224 * (∫ g : G, chi g ∂mu) - 531 := by
      rw [integral_sub hIntL (integrable_const _)]
      rw [integral_sub (hIntA.const_mul _) (hIntChi.const_mul _)]
      simp [integral_const_mul]
    _ = 1781 := by
      rw [p4Q2PZ37AFS_shiftedSquare_integral_half,
        p4Q2PZ37AFS_originalCharacter_mean_zero]
      norm_num

/-- The true 4/5 ball sits inside the improved Markov event. -/
theorem p4Q2PZ37AFT_originalBall_subset_optimalMarkovEvent :
    BallJ (1 : G) (4 / 5) ⊆
      {g : G | (3171961 / 625 : ℝ) ≤
        p4Q2PZ37AFT_optimalMarkovSquare g} := by
  intro g hg
  have hchi := p4Q2PZ37AFS_trueBall_character_gt g hg
  have hlin : (1781 / 25 : ℝ) < 68 * chi g + 25 := by
    linarith only [hchi]
  change (3171961 / 625 : ℝ) ≤ p4Q2PZ37AFT_optimalMarkovSquare g
  unfold p4Q2PZ37AFT_optimalMarkovSquare
  nlinarith only [hlin]

/-- One-sided second-moment/Cantelli-optimal bound for the same true Haar ball. -/
theorem p4Q2PZ37AFT_originalRadialHaar_fourFifths_le :
    m (4 / 5) ≤ (625 / 1781 : ℝ) := by
  have hMarkov :
      (3171961 / 625 : ℝ) *
        Measure.real mu
          {g : G | (3171961 / 625 : ℝ) ≤
            p4Q2PZ37AFT_optimalMarkovSquare g}
        ≤ (1781 : ℝ) := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := mu) (f := p4Q2PZ37AFT_optimalMarkovSquare)
      (Filter.Eventually.of_forall p4Q2PZ37AFT_optimalMarkovSquare_nonneg)
      p4Q2PZ37AFT_optimalMarkovSquare_integrable (3171961 / 625)
    rw [p4Q2PZ37AFT_optimalMarkovSquare_integral] at h
    exact h
  have hSub : m (4 / 5) ≤
      Measure.real mu
        {g : G | (3171961 / 625 : ℝ) ≤
          p4Q2PZ37AFT_optimalMarkovSquare g} :=
    measureReal_mono
      p4Q2PZ37AFT_originalBall_subset_optimalMarkovEvent (measure_ne_top _ _)
  nlinarith only [hMarkov, hSub]

theorem p4Q2PZ37AFT_radialHaar_strictlyImproves_AFS :
    m (4 / 5) ≤ (625 / 1781 : ℝ) ∧
      (625 / 1781 : ℝ) < 1250 / 3481 := by
  constructor
  · exact p4Q2PZ37AFT_originalRadialHaar_fourFifths_le
  · norm_num

/-- Transfer by genuine original Haar translation and AFQ cell containment. -/
theorem p4Q2PZ37AFT_everyCell_originalHaar_le
    (i : Fin (Fintype.card Grid)) :
    Measure.real mu (p4Q2PZ37AFQ_cells i) ≤ (625 / 1781 : ℝ) := by
  have hSub :
      p4Q2PZ37AFQ_cells i ⊆ BallJ (gridCenter i) (4 / 5) := by
    intro g hg
    exact (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      (Fintype.card Grid) center (4 / 5) i g).1 hg |>.1
  calc
    Measure.real mu (p4Q2PZ37AFQ_cells i) ≤
        Measure.real mu (BallJ (gridCenter i) (4 / 5)) :=
      measureReal_mono hSub (measure_ne_top _ _)
    _ = m (4 / 5) :=
      p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial _ _
    _ ≤ 625 / 1781 :=
      p4Q2PZ37AFT_originalRadialHaar_fourFifths_le

theorem p4Q2PZ37AFT_everyCell_originalHaar_interval
    (i : Fin (Fintype.card Grid)) :
    (1 / 160000 : ℝ) ≤ Measure.real mu (p4Q2PZ37AFQ_cells i) ∧
      Measure.real mu (p4Q2PZ37AFQ_cells i) ≤ (625 / 1781 : ℝ) :=
  ⟨p4Q2PZ37AFR_everyCell_originalHaar_ge_rational i,
   p4Q2PZ37AFT_everyCell_originalHaar_le i⟩

/-- A strictly tighter, fixed-rational error for w_i = 1/24. -/
theorem p4Q2PZ37AFT_fixedWeight_accuracy
    (i : Fin (Fintype.card Grid)) :
    |Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ)| ≤ (13219 / 42744 : ℝ) := by
  obtain ⟨hLo,hHi⟩ := p4Q2PZ37AFT_everyCell_originalHaar_interval i
  have hw : (p4Q2PZ37AFR_fixedWeight i : ℝ) = (1 / 24 : ℝ) := by
    norm_num [p4Q2PZ37AFR_fixedWeight]
  rw [hw]
  exact abs_le.mpr ⟨by linarith only [hLo], by linarith only [hHi]⟩

theorem p4Q2PZ37AFT_fixedError_strictlyImproves_AFS :
    (13219 / 42744 : ℝ) < 26519 / 83544 := by
  norm_num

/-- Effective unchanged 24-cell probability vector, improved mass error. -/
def p4Q2PZ37AFT_originalOptimalHaarCells :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := Fintype.card Grid
  cell := p4Q2PZ37AFQ_cells
  hMeas := p4Q2PZ37AFQ_cells_measurable
  hPartition := p4Q2PZ37AFQ_cells_partition
  weight := p4Q2PZ37AFR_fixedWeight
  weightError := fun _ => (13219 / 42744 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy := p4Q2PZ37AFT_fixedWeight_accuracy

/-- Every rational quadrature table benefits weakly from this tightening;
nonzero tables benefit strictly. Zero-sample physical fallback has zero
weight-error term regardless of the Haar enclosure. -/
theorem p4Q2PZ37AFT_HaarWeightError_le_AFS
    (q : Fin (Fintype.card Grid) → ℚ) :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarWeightError
        p4Q2PZ37AFT_originalOptimalHaarCells q ≤
      GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarWeightError
        p4Q2PZ37AFS_originalMomentTightenedHaarCells q := by
  change
    (∑ i : Fin (Fintype.card Grid),
      |(q i : ℝ)| * (13219 / 42744 : ℝ)) ≤
    ∑ i : Fin (Fintype.card Grid),
      |(q i : ℝ)| * (26519 / 83544 : ℝ)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (le_of_lt p4Q2PZ37AFT_fixedError_strictlyImproves_AFS) (abs_nonneg _)

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "F" =>
  p4Q2PZ37ABZ_originalReceiverSection H p4Q2PZ37ADC_fixedCoupling
    p4Q2PZ37ADC_fixedCoupling_pos.le
    (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AFT_links : Fintype Link := Fintype.ofFinite _

/-- The only remaining input is *verified numerical data* at the
24 original quaternion centers. No external geometric, receiver-envelope,
or measure choices are permitted. Nonzero rational samples are allowed. -/
structure p4Q2PZ37AFT_original24CellVerifiedSamples
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  meanSample : Pair → Fin (Fintype.card Grid) → ℚ
  meanSampleError : Pair → ℝ
  hMeanSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ meanSampleError a
  hMeanSample : ∀ a ∈ c.s, ∀ i,
    |F e a (gridCenter i) - (meanSample a i : ℝ)| ≤ meanSampleError a
  secondSample : Pair → Fin (Fintype.card Grid) → ℚ
  secondSampleError : Pair → ℝ
  hSecondSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ secondSampleError a
  hSecondSample : ∀ a ∈ c.s, ∀ i,
    |(F e a (gridCenter i)) ^ 2 - (secondSample a i : ℝ)| ≤
      secondSampleError a
  coefficientSample : Pair → Fin 4 → Fin (Fintype.card Grid) → ℚ
  coefficientSampleError : Pair → Fin 4 → ℝ
  hCoefficientSampleError_nonneg : ∀ a ∈ c.s, ∀ j,
    0 ≤ coefficientSampleError a j
  hCoefficientSample : ∀ a ∈ c.s, ∀ j i,
    |F e a (gridCenter i) * p4Q2PZ37ACK_fourModeCharacter j (gridCenter i) -
      (coefficientSample a j i : ℝ)| ≤ coefficientSampleError a j

/-- No assumptions about cell geometry or physical Lipschitz constants:
these are discharged by AFQ and AFM in the ORIGINAL SU(2) gauge system. -/
def p4Q2PZ37AFT_toOriginalPhysicalSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c) :
    p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c where
  partition := p4Q2PZ37AFT_originalOptimalHaarCells
  center := p4Q2PZ37AFQ_originalCenters
  radius := 4 / 5
  hRadius := by norm_num
  hCellRadius := p4Q2PZ37AFQ_cells_chordalRadius
  hThetaLo := hlo
  meanSample := d.meanSample
  meanSampleError := d.meanSampleError
  hMeanSampleError_nonneg := d.hMeanSampleError_nonneg
  hMeanSample := d.hMeanSample
  secondSample := d.secondSample
  secondSampleError := d.secondSampleError
  hSecondSampleError_nonneg := d.hSecondSampleError_nonneg
  hSecondSample := d.hSecondSample
  coefficientSample := d.coefficientSample
  coefficientSampleError := d.coefficientSampleError
  hCoefficientSampleError_nonneg := d.hCoefficientSampleError_nonneg
  hCoefficientSample := d.hCoefficientSample

/-- The AFJ quadrature now uses the *explicit* optimized AFT Haar cells. -/
def p4Q2PZ37AFT_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFM_toOriginalReceiverQuadrature
    H e c (p4Q2PZ37AFT_toOriginalPhysicalSamples H e c hlo d)

/-- Typechecked direct link: true physical AFM -> AFI coefficient/variance. -/
def p4Q2PZ37AFT_toOriginalCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    H e c (p4Q2PZ37AFT_toOriginalPhysicalSamples H e c hlo d)

/-- Explicit identity of the genuine Haar weight error passed to physical
quadrature for ANY independently verified (possibly nonzero) sample table. -/
theorem p4Q2PZ37AFT_physicalQuadrature_optimizedHaarWeightError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c)
    (q : Fin (Fintype.card Grid) → ℚ) :
    p4Q2PZ37AFJ_HaarWeightError
      (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d).partition q =
      ∑ i : Fin (Fintype.card Grid),
        |(q i : ℝ)| * (13219 / 42744 : ℝ) := by
  rfl

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_rationalShift_optimal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_rationalShift_attains_optimum
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_optimalMarkovSquare_linearAFS
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_optimalMarkovSquare_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_optimalMarkovSquare_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_optimalMarkovSquare_integral
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_originalBall_subset_optimalMarkovEvent
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_originalRadialHaar_fourFifths_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_radialHaar_strictlyImproves_AFS
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_everyCell_originalHaar_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_everyCell_originalHaar_interval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_fixedWeight_accuracy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_fixedError_strictlyImproves_AFS
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFT_HaarWeightError_le_AFS
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFT_physicalQuadrature_optimizedHaarWeightError
