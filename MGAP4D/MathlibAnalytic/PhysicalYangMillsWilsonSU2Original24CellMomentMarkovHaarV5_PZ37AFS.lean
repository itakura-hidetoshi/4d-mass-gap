import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2Original24CellEffectiveHaarV5_PZ37AFR
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFS — original SU(2) second-moment Haar mass tightening

AFR proved positive rational bounds for all twenty-four true first-center
SU(2) Borel cells, but the upper mass 1/2 made its effective weights
coarse. AFS uses the ALREADY-PROVED genuine Wilson quaternion Haar
Gram matrix, without any new distribution or surrogate gauge theory.

For the ORIGINAL real Wilson fundamental character chi(g)=1-E(g),
the genuine compact Haar law has E[chi]=0 and E[chi^2]=1/4.
The manifestly nonnegative original observable

     P(g) = (chi(g) + 1/2)^2

therefore has E[P]=1/2. On the literal original open chordal ball
B_J(1,4/5), ADK's Wilson calibration gives chi(g)>17/25,
hence P(g)>(59/50)^2=3481/2500.

The fixed pinned-mathlib real Markov inequality now yields

     m(4/5) <= 1250/3481 < 1/2.

Every AFR/AFQ genuine Borel cell lies inside its own true
radius-4/5 SU(2) ball. Haar translation invariance propagates the
new upper bound to all twenty-four genuine cells. The SAME original
positive inner core remains, hence

     1/160000 <= Haar(C_i) <= 1250/3481.

Fully explicit rational weights w_i=1/24, summing to one, now have
the tightened certified error 26519/83544, not 11/24.
This is a rigorously checked rational *enclosure*, not a numerical
evaluation of actual Haar cell masses. No unproved two-sign physical
crossing or H-uniform coercivity/Hamiltonian/continuum mass gap.
All physical FF/Perron/Wilson sources and original Haar are preserved.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "center" => p4Q2PZ37AFQ_originalCenters

local instance p4Q2PZ37AFS_topological : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFS_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFS_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFS_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFS_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFS_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Exact original zero mean from the proven quaternion Haar character. -/
theorem p4Q2PZ37AFS_originalCharacter_mean_zero :
    (∫ g : G, chi g ∂mu) = 0 := by
  simpa only [p4Q2PZ37ACK_fourModeCharacter_zero] using
    (p4Q2PZ37ACK_fourModeCharacter_mean_zero (0 : Fin 4))

/-- ORIGINAL normalized Haar square moment, not a proxy S³ integral. -/
theorem p4Q2PZ37AFS_originalCharacter_square_integral :
    (∫ g : G, (chi g) ^ 2 ∂mu) = (1 / 4 : ℝ) := by
  have h := p4Q2PZ37ACK_fourModeCharacter_gram (0 : Fin 4) (0 : Fin 4)
  have hg :
      (∫ g : G,
        p4Q2PZ37ACK_fourModeCharacter 0 g *
          p4Q2PZ37ACK_fourModeCharacter 0 g ∂mu) = (1 / 4 : ℝ) := by
    simpa using h
  simpa only [p4Q2PZ37ACK_fourModeCharacter_zero, pow_two] using hg

/-- A nonnegative POLYNOMIAL of the ORIGINAL physical Wilson character.
It is deliberately expanded for the pinned Bochner integral linearity API. -/
def p4Q2PZ37AFS_shiftedSquare (g : G) : ℝ :=
  (chi g) ^ 2 + chi g + 1 / 4

theorem p4Q2PZ37AFS_shiftedSquare_eq_square (g : G) :
    p4Q2PZ37AFS_shiftedSquare g = (chi g + 1 / 2) ^ 2 := by
  unfold p4Q2PZ37AFS_shiftedSquare
  ring

theorem p4Q2PZ37AFS_shiftedSquare_nonneg (g : G) :
    0 ≤ p4Q2PZ37AFS_shiftedSquare g := by
  rw [p4Q2PZ37AFS_shiftedSquare_eq_square]
  exact sq_nonneg _

theorem p4Q2PZ37AFS_shiftedSquare_integrable :
    Integrable p4Q2PZ37AFS_shiftedSquare mu := by
  have hc : Continuous chi :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hP : Continuous p4Q2PZ37AFS_shiftedSquare := by
    unfold p4Q2PZ37AFS_shiftedSquare
    exact ((hc.pow 2).add hc).add continuous_const
  exact hP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Certified true Haar expectation E[(chi+1/2)^2] = 1/2. -/
theorem p4Q2PZ37AFS_shiftedSquare_integral_half :
    (∫ g : G, p4Q2PZ37AFS_shiftedSquare g ∂mu) = (1 / 2 : ℝ) := by
  have hc : Continuous chi :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hInt : Integrable chi mu :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntSq : Integrable (fun g : G => (chi g) ^ 2) mu :=
    (hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ g : G, p4Q2PZ37AFS_shiftedSquare g ∂mu) =
        (∫ g : G, (chi g) ^ 2 ∂mu) +
          (∫ g : G, chi g ∂mu) + 1 / 4 := by
      have hSplit1 :
          (∫ g : G, ((chi g) ^ 2 + chi g) + (1 / 4 : ℝ) ∂mu) =
            (∫ g : G, (chi g) ^ 2 + chi g ∂mu) +
              (∫ _g : G, (1 / 4 : ℝ) ∂mu) :=
        integral_add (hIntSq.add hInt) (integrable_const _)
      have hSplit2 :
          (∫ g : G, (chi g) ^ 2 + chi g ∂mu) =
            (∫ g : G, (chi g) ^ 2 ∂mu) +
              (∫ g : G, chi g ∂mu) :=
        integral_add hIntSq hInt
      change (∫ g : G, ((chi g) ^ 2 + chi g) + (1 / 4 : ℝ) ∂mu) =
        (∫ g : G, (chi g) ^ 2 ∂mu) +
          (∫ g : G, chi g ∂mu) + 1 / 4
      rw [hSplit1, hSplit2]
      simp
    _ = 1 / 2 := by
      rw [p4Q2PZ37AFS_originalCharacter_square_integral,
        p4Q2PZ37AFS_originalCharacter_mean_zero]
      norm_num

/-- On the unchanged original ADK radius-4/5 ball the fundamental
character is strictly greater than the RATIONAL threshold 17/25. -/
theorem p4Q2PZ37AFS_trueBall_character_gt (g : G)
    (hg : g ∈ BallJ (1 : G) (4 / 5)) :
    (17 / 25 : ℝ) < chi g := by
  have hDist : dJ (1 : G) g < (4 / 5 : ℝ) := hg
  have hNN : 0 ≤ dJ (1 : G) g :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  have hSq : (dJ (1 : G) g) ^ 2 = 2 * E g := by
    simpa only [inv_one, one_mul] using
      (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (1 : G) g)
  have hUpper : (dJ (1 : G) g) ^ 2 < (16 / 25 : ℝ) := by
    nlinarith only [hDist, hNN]
  dsimp [p4Q2PZ35C_originalOneLinkCharacter]
  linarith only [hSq, hUpper]

/-- The TRUE radius-4/5 ball is contained in the fixed Markov event.
No assumed numerical sphere cap law is used. -/
theorem p4Q2PZ37AFS_trueBall_subset_shiftedSquareEvent :
    BallJ (1 : G) (4 / 5) ⊆
      {g : G | (3481 / 2500 : ℝ) ≤ p4Q2PZ37AFS_shiftedSquare g} := by
  intro g hg
  have hChar := p4Q2PZ37AFS_trueBall_character_gt g hg
  have hPlus : (59 / 50 : ℝ) < chi g + 1 / 2 := by
    linarith only [hChar]
  have hSq : (3481 / 2500 : ℝ) ≤ (chi g + 1 / 2) ^ 2 := by
    nlinarith only [hPlus]
  change (3481 / 2500 : ℝ) ≤ p4Q2PZ37AFS_shiftedSquare g
  rw [p4Q2PZ37AFS_shiftedSquare_eq_square]
  exact hSq

/-- REAL Markov inequality, pinned mathlib: a numerical, unconditional
upper bound on the SAME normalized original SU(2) Haar-ball mass. -/
theorem p4Q2PZ37AFS_originalRadialHaar_fourFifths_le :
    m (4 / 5) ≤ (1250 / 3481 : ℝ) := by
  have hMarkov :
      (3481 / 2500 : ℝ) *
        Measure.real mu
          {g : G | (3481 / 2500 : ℝ) ≤ p4Q2PZ37AFS_shiftedSquare g}
        ≤ (1 / 2 : ℝ) := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := mu) (f := p4Q2PZ37AFS_shiftedSquare)
      (Filter.Eventually.of_forall p4Q2PZ37AFS_shiftedSquare_nonneg)
      p4Q2PZ37AFS_shiftedSquare_integrable (3481 / 2500)
    rw [p4Q2PZ37AFS_shiftedSquare_integral_half] at h
    exact h
  have hSub : m (4 / 5) ≤
      Measure.real mu
        {g : G | (3481 / 2500 : ℝ) ≤ p4Q2PZ37AFS_shiftedSquare g} := by
    exact measureReal_mono
      p4Q2PZ37AFS_trueBall_subset_shiftedSquareEvent (measure_ne_top _ _)
  nlinarith only [hMarkov, hSub]

/-- The new true Haar upper bound is STRICTLY sharper than AFR's 1/2. -/
theorem p4Q2PZ37AFS_radialHaar_bound_lt_half :
    m (4 / 5) < (1 / 2 : ℝ) := by
  have h := p4Q2PZ37AFS_originalRadialHaar_fourFifths_le
  linarith only [h]

/-- Every AFQ true first-center Borel cell inherits the SAME tightened
genuine Haar radial upper bound, using ADM center independence. -/
theorem p4Q2PZ37AFS_everyCell_originalHaar_le
    (i : Fin (Fintype.card Grid)) :
    Measure.real mu (p4Q2PZ37AFQ_cells i) ≤ (1250 / 3481 : ℝ) := by
  have hSub :
      p4Q2PZ37AFQ_cells i ⊆ BallJ (center i) (4 / 5) := by
    intro g hg
    exact (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      (Fintype.card Grid) center (4 / 5) i g).1 hg |>.1
  calc
    Measure.real mu (p4Q2PZ37AFQ_cells i) ≤
        Measure.real mu (BallJ (center i) (4 / 5)) :=
      measureReal_mono hSub (measure_ne_top _ _)
    _ = m (4 / 5) :=
      p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial _ _
    _ ≤ 1250 / 3481 :=
      p4Q2PZ37AFS_originalRadialHaar_fourFifths_le

theorem p4Q2PZ37AFS_everyCell_originalHaar_rationalInterval
    (i : Fin (Fintype.card Grid)) :
    (1 / 160000 : ℝ) ≤ Measure.real mu (p4Q2PZ37AFQ_cells i) ∧
      Measure.real mu (p4Q2PZ37AFQ_cells i) ≤ (1250 / 3481 : ℝ) :=
  ⟨p4Q2PZ37AFR_everyCell_originalHaar_ge_rational i,
   p4Q2PZ37AFS_everyCell_originalHaar_le i⟩

/-- Effective fixed 24 rational weights now have a smaller
PROVED absolute Haar error than AFR's original 11/24. -/
theorem p4Q2PZ37AFS_fixedWeight_accuracy
    (i : Fin (Fintype.card Grid)) :
    |Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ)| ≤ (26519 / 83544 : ℝ) := by
  obtain ⟨hLo,hHi⟩ := p4Q2PZ37AFS_everyCell_originalHaar_rationalInterval i
  have hw :
      (p4Q2PZ37AFR_fixedWeight i : ℝ) = (1 / 24 : ℝ) := by
    norm_num [p4Q2PZ37AFR_fixedWeight]
  rw [hw]
  exact abs_le.mpr ⟨by linarith only [hLo], by linarith only [hHi]⟩

/-- True AFJ Haar certificate with the SAME literal 1/24 weights,
but materially tighter proven real-Haar error 26519/83544.
No noncomputable rational mass choice is made. -/
def p4Q2PZ37AFS_originalMomentTightenedHaarCells :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := Fintype.card Grid
  cell := p4Q2PZ37AFQ_cells
  hMeas := p4Q2PZ37AFQ_cells_measurable
  hPartition := p4Q2PZ37AFQ_cells_partition
  weight := p4Q2PZ37AFR_fixedWeight
  weightError := fun _ => (26519 / 83544 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy := p4Q2PZ37AFS_fixedWeight_accuracy

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_originalCharacter_mean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_originalCharacter_square_integral
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_shiftedSquare_eq_square
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_shiftedSquare_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_shiftedSquare_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_shiftedSquare_integral_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_trueBall_character_gt
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_trueBall_subset_shiftedSquareEvent
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_originalRadialHaar_fourFifths_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_radialHaar_bound_lt_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_everyCell_originalHaar_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_everyCell_originalHaar_rationalInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFS_fixedWeight_accuracy
