import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2Original24CellSphereGridV5_PZ37AFQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitSpherePolynomialFloorV5_PZ37AEC
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFR — effective ORIGINAL SU(2) 24-cell Haar enclosures

AFQ supplied 24 explicit original SU(2) centers and an OPEN original
4/5-chordal cover, but its rational Haar weights are NONCOMPUTABLE
real-density choices. AFR strengthens the geometric certificate.

The same 24 genuine S³ vertices, each specified by rational
four-coordinate data, are 1-separated. Therefore the genuine open
chordal ball B_J(c_i,1/5) lies inside the AFQ first-covering-center
Borel cell C_i at radius 4/5, regardless of the arbitrary ordering.
The unconditional ADZ/AEC ORIGINAL Haar ball floor then gives the
LITERAL rational inequality

       1/160000 <= normalizedCompactHaar_SU2(C_i) <= 1/2

for EVERY one of the 24 indexed, nonempty positive-mass cells.
No numerical Haar integral or proxy finite counting Haar is used.

The same 24-center cover also gives a separate sharp explicit
reciprocal cover floor m(4/5) >= 1/24 using the prior ADP finite-net
Haar theorem. No unproved numerical equidistribution is assumed.

For the same original true Haar cells, the computable rational
weights w_i=1/24 are all positive and sum exactly to 1. Their
CERTIFIED coarse per-cell error 11/24 is deliberately not confused
with AFQ's finer but NONCOMPUTABLE 1/64 rational enclosure.
The true signed FF physical source, Perron kernel, original BCF
receiver, four character modes, pair Haar, AFG independent samples,
and AFM->AFI certificate chain are retained without modification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
set_option maxRecDepth 8192

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "center" => p4Q2PZ37AFQ_originalCenters
local notation "sphereCenter" => p4Q2PZ37AFQ_sphereGridCenter
local notation "Φ" => p4Q2PZ37ADR_originalSU2ToSphere
local notation "Ψ" => p4Q2PZ37ADS_originalSphereToSU2
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "mu" => normalizedCompactHaar G
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

local instance p4Q2PZ37AFR_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFR_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFR_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFR_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFR_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFR_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Twice the original vertex coordinates, now all INTEGERS.
The exact finite arithmetic proof uses no rational gcd reduction. -/
def p4Q2PZ37AFR_vertexZ (i : Grid) (k : Fin 4) : ℤ :=
  match i with
  | Sum.inl (j,s) =>
      if k = j then (if s then -2 else 2) else 0
  | Sum.inr s =>
      if s k then -1 else 1

/-- Recover original SU(2) sphere coordinates exactly from
the finite integer representation by division by two. -/
theorem p4Q2PZ37AFR_vertexZ_eq_real
    (i : Grid) (k : Fin 4) :
    ((sphereCenter i : S3) : E4) k = (p4Q2PZ37AFR_vertexZ i k : ℝ) / 2 := by
  cases i with
  | inl p =>
      rcases p with ⟨j,s⟩
      by_cases h : k = j
      · subst k
        cases s <;>
          norm_num [p4Q2PZ37AFR_vertexZ, p4Q2PZ37AFQ_sphereGridCenter,
            p4Q2PZ37AFQ_axisSphere, p4Q2PZ37AFQ_axisVector]
      · cases s <;>
          simp [p4Q2PZ37AFR_vertexZ, p4Q2PZ37AFQ_sphereGridCenter,
            p4Q2PZ37AFQ_axisSphere, p4Q2PZ37AFQ_axisVector, h]
  | inr s =>
      cases h : s k <;>
        norm_num [p4Q2PZ37AFR_vertexZ, p4Q2PZ37AFQ_sphereGridCenter,
          p4Q2PZ37AFQ_diagSphere, p4Q2PZ37AFQ_diagVector, h]

/-- Finite integer certificate: for 24 different vertices the
dot product of TWICE their coordinates is at most 2. -/
theorem p4Q2PZ37AFR_vertexZ_inner_le_two :
    ∀ i j : Grid, i ≠ j →
      (∑ k : Fin 4,
        p4Q2PZ37AFR_vertexZ i k *
          p4Q2PZ37AFR_vertexZ j k) ≤ (2 : ℤ) := by
  intro i j hij
  cases i with
  | inl p =>
      rcases p with ⟨a,sa⟩
      cases j with
      | inl q =>
          rcases q with ⟨b,sb⟩
          fin_cases a <;> fin_cases b <;>
            cases sa <;> cases sb <;>
            first
            | exact False.elim (by simpa using hij)
            | norm_num [p4Q2PZ37AFR_vertexZ, Fin.sum_univ_four]
      | inr t =>
          fin_cases a <;> cases sa <;>
            simp [p4Q2PZ37AFR_vertexZ] <;>
            split_ifs <;> omega
  | inr s =>
      cases j with
      | inl q =>
          rcases q with ⟨b,sb⟩
          fin_cases b <;> cases sb <;>
            simp [p4Q2PZ37AFR_vertexZ] <;>
            split_ifs <;> omega
      | inr t =>
          have hst : s ≠ t := by
            intro he
            exact hij (congrArg Sum.inr he)
          have hSome : ∃ k : Fin 4, s k ≠ t k := by
            by_contra hh
            apply hst
            funext k
            by_contra hk
            exact hh ⟨k, hk⟩
          have hTerm (k : Fin 4) :
              p4Q2PZ37AFR_vertexZ (Sum.inr s) k *
                p4Q2PZ37AFR_vertexZ (Sum.inr t) k ≤ (1 : ℤ) := by
            cases hs : s k <;> cases ht : t k <;>
              norm_num [p4Q2PZ37AFR_vertexZ, hs, ht]
          have hOpp (k : Fin 4) (hk : s k ≠ t k) :
              p4Q2PZ37AFR_vertexZ (Sum.inr s) k *
                p4Q2PZ37AFR_vertexZ (Sum.inr t) k = (-1 : ℤ) := by
            cases hs : s k <;> cases ht : t k <;>
              simp_all [p4Q2PZ37AFR_vertexZ]
          obtain ⟨k, hk⟩ := hSome
          have h0 := hTerm 0
          have h1 := hTerm 1
          have h2 := hTerm 2
          have h3 := hTerm 3
          have hh := hOpp k hk
          simp only [Fin.sum_univ_four]
          fin_cases k
          · have heq :
                p4Q2PZ37AFR_vertexZ (Sum.inr s) 0 *
                  p4Q2PZ37AFR_vertexZ (Sum.inr t) 0 = (-1 : ℤ) := by
              simpa using hh
            omega
          · have heq :
                p4Q2PZ37AFR_vertexZ (Sum.inr s) 1 *
                  p4Q2PZ37AFR_vertexZ (Sum.inr t) 1 = (-1 : ℤ) := by
              simpa using hh
            omega
          · have heq :
                p4Q2PZ37AFR_vertexZ (Sum.inr s) 2 *
                  p4Q2PZ37AFR_vertexZ (Sum.inr t) 2 = (-1 : ℤ) := by
              simpa using hh
            omega
          · have heq :
                p4Q2PZ37AFR_vertexZ (Sum.inr s) 3 *
                  p4Q2PZ37AFR_vertexZ (Sum.inr t) 3 = (-1 : ℤ) := by
              simpa using hh
            omega

/-- Original S³ inner products inherit the kernel-checked
finite integer certificate (dot<=2 corresponds to dot<=1/2). -/
theorem p4Q2PZ37AFR_sphereGrid_inner_le_half
    (i j : Grid) (hij : i ≠ j) :
    inner ℝ (sphereCenter i : E4) (sphereCenter j : E4) ≤ (1/2 : ℝ) := by
  have hz := p4Q2PZ37AFR_vertexZ_inner_le_two i j hij
  have hr :
      (∑ k : Fin 4,
        (p4Q2PZ37AFR_vertexZ i k : ℝ) *
          (p4Q2PZ37AFR_vertexZ j k : ℝ)) ≤ (2 : ℝ) := by
    exact_mod_cast hz
  have hEq :
      4 * inner ℝ (sphereCenter i : E4) (sphereCenter j : E4) =
        ∑ k : Fin 4,
          (p4Q2PZ37AFR_vertexZ i k : ℝ) *
            (p4Q2PZ37AFR_vertexZ j k : ℝ) := by
    rw [PiLp.inner_apply]
    simp_rw [realScalarInner_eq_mul, p4Q2PZ37AFR_vertexZ_eq_real]
    simp only [Fin.sum_univ_four]
    ring
  linarith only [hr, hEq]

/-- Distinct rational grid vertices are at Euclidean chord distance
AT LEAST 1, matching the existing original true J-chord metric. -/
theorem p4Q2PZ37AFR_originalGrid_separated
    (i j : Grid) (hij : i ≠ j) :
    1 ≤ dJ (Ψ (sphereCenter i)) (Ψ (sphereCenter j)) := by
  have hX (t : Grid) :
      V (Ψ (sphereCenter t)) = (sphereCenter t : E4) := by
    simpa only [p4Q2PZ37ADR_originalSU2ToSphere] using
      (congrArg Subtype.val
        (p4Q2PZ37ADS_sphere_roundtrip (sphereCenter t)))
  have hSq :
      (dJ (Ψ (sphereCenter i)) (Ψ (sphereCenter j))) ^ 2 =
        2 - 2 * inner ℝ (sphereCenter i : E4) (sphereCenter j : E4) := by
    rw [p4Q2PZ37ADT_originalChordal_sq_eq_sphereChord_sq,
      norm_sub_sq_real,
      p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one,
      p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one,
      hX, hX]
    ring
  have hInner := p4Q2PZ37AFR_sphereGrid_inner_le_half i j hij
  have hNN : 0 ≤ dJ (Ψ (sphereCenter i)) (Ψ (sphereCenter j)) :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  nlinarith only [hSq, hInner, hNN]

/-- The exact AFQ Fin24 enumeration is ALSO 1-separated.
This prevents coincident centers and certifies disjoint tiny cores. -/
theorem p4Q2PZ37AFR_originalCenters_separated
    (i j : Fin (Fintype.card Grid)) (hij : i ≠ j) :
    1 ≤ dJ (center i) (center j) := by
  let e := Fintype.equivFin Grid
  have hindex : e.symm i ≠ e.symm j := by
    intro h
    apply hij
    simpa using congrArg e h
  exact p4Q2PZ37AFR_originalGrid_separated
    (e.symm i) (e.symm j) hindex

/-- Each genuinely separated center has a fixed open 1/5-core
which is NOT preempted by any earlier radius-4/5 ball. -/
theorem p4Q2PZ37AFR_originalSmallBall_subset_cell
    (i : Fin (Fintype.card Grid)) :
    BallJ (center i) (1 / 5) ⊆ p4Q2PZ37AFQ_cells i := by
  intro g hg
  apply (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
    (Fintype.card Grid) center (4 / 5) i g).2
  constructor
  · change dJ (center i) g < (4 / 5 : ℝ)
    have hi : dJ (center i) g < (1 / 5 : ℝ) := hg
    linarith
  · intro j hji hj
    have hSep : (1 : ℝ) ≤ dJ (center i) (center j) :=
      p4Q2PZ37AFR_originalCenters_separated i j (ne_of_gt hji)
    have hTriangle : dJ (center i) (center j) ≤
        dJ (center i) g + dJ g (center j) :=
      p4Q2PZ37ADK_trueChordalDistance_triangle _ _ _
    have hi : dJ (center i) g < (1 / 5 : ℝ) := hg
    have hj' : dJ g (center j) < (4 / 5 : ℝ) := by
      rw [p4Q2PZ37ADK_trueChordalDistance_symm]
      exact hj
    linarith

/-- Fully effective rational lower Haar bound, for EVERY ONE
of the 24 genuine AFQ Borel cells, with no mass evaluation. -/
theorem p4Q2PZ37AFR_everyCell_originalHaar_ge_rational
    (i : Fin (Fintype.card Grid)) :
    (1 / 160000 : ℝ) ≤ Measure.real mu (p4Q2PZ37AFQ_cells i) := by
  have hBall := p4Q2PZ37ADZ_originalAllCenters_ge_explicit
    (center i) (1 / 5) (by norm_num)
  rw [p4Q2PZ37AEC_originalKappa_eq_smallQuartic
    (1 / 5) (by norm_num) (by norm_num)] at hBall
  have hRational : (1 / 160000 : ℝ) ≤
      Measure.real mu (BallJ (center i) (1 / 5)) := by
    norm_num at hBall ⊢
    exact hBall
  exact hRational.trans
    (measureReal_mono (p4Q2PZ37AFR_originalSmallBall_subset_cell i)
      (measure_ne_top _ _))

/-- All 24 genuinely positive Borel cells retain the antipodal
Haar ball upper bound at the unchanged physical radius 4/5. -/
theorem p4Q2PZ37AFR_everyCell_originalHaar_le_half
    (i : Fin (Fintype.card Grid)) :
    Measure.real mu (p4Q2PZ37AFQ_cells i) ≤ (1 / 2 : ℝ) := by
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
    _ ≤ 1 / 2 :=
      p4Q2PZ37ADN_radialMass_le_half (4 / 5)
        (by norm_num) (by norm_num)

/-- A checkable FINSET of at most 24 ACTUAL SU(2) matrices,
all providing genuine radius-4/5 open Wilson balls. -/
def p4Q2PZ37AFR_originalFiniteCenterSet : Finset G :=
  Finset.univ.image center

theorem p4Q2PZ37AFR_originalFiniteCenterSet_card_le_24 :
    p4Q2PZ37AFR_originalFiniteCenterSet.card ≤ 24 := by
  calc
    p4Q2PZ37AFR_originalFiniteCenterSet.card ≤
        (Finset.univ : Finset (Fin (Fintype.card Grid))).card :=
      Finset.card_image_le
    _ = 24 := by
      simp

theorem p4Q2PZ37AFR_originalFiniteCenterSet_isNet :
    p4Q2PZ37ADP_isTrueChordalNet
      p4Q2PZ37AFR_originalFiniteCenterSet (4 / 5) := by
  intro g
  obtain ⟨i, hi⟩ := p4Q2PZ37AFQ_originalCenters_openCover g
  refine ⟨center i, ?_, hi⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- An improved and fully explicit ORIGINAL Haar ball MASS LOWER:
1/24, not the quartic analytic lower at 4/5. -/
theorem p4Q2PZ37AFR_trueRadialHaar_fourFifths_ge_oneOver24 :
    (1 / 24 : ℝ) ≤ m (4 / 5) := by
  have h := p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_inverse_budget
    p4Q2PZ37AFR_originalFiniteCenterSet (4 / 5) 24
    p4Q2PZ37AFR_originalFiniteCenterSet_isNet
    p4Q2PZ37AFR_originalFiniteCenterSet_card_le_24
  norm_num at h ⊢
  exact h

/-- Explicit fixed rational weights, not a classical choice or
dependent on uncomputed Haar masses. -/
def p4Q2PZ37AFR_fixedWeight (_i : Fin (Fintype.card Grid)) : ℚ :=
  1 / 24

theorem p4Q2PZ37AFR_fixedWeight_sum_one :
    (∑ i : Fin (Fintype.card Grid),
      p4Q2PZ37AFR_fixedWeight i) = (1 : ℚ) := by
  norm_num [p4Q2PZ37AFR_fixedWeight,
    p4Q2PZ37AFQ_gridIndex_card]

theorem p4Q2PZ37AFR_fixedWeight_pos
    (i : Fin (Fintype.card Grid)) :
    0 < p4Q2PZ37AFR_fixedWeight i := by
  norm_num [p4Q2PZ37AFR_fixedWeight]

/-- Fully checkable conservative error of actual rational weights
on the true original Haar cells. This is numerically COARSER
than AFQ's noncomputable density approximation, intentionally. -/
theorem p4Q2PZ37AFR_fixedWeight_accuracy
    (i : Fin (Fintype.card Grid)) :
    |Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ)| ≤ (11 / 24 : ℝ) := by
  have hLo := p4Q2PZ37AFR_everyCell_originalHaar_ge_rational i
  have hHi := p4Q2PZ37AFR_everyCell_originalHaar_le_half i
  have hW : (p4Q2PZ37AFR_fixedWeight i : ℝ) = (1 / 24 : ℝ) := by
    norm_num [p4Q2PZ37AFR_fixedWeight]
  rw [hW]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual original Haar finite-cell certificate using the fixed,
rational probability vector 1/24 and coarse but PROVED errors. -/
def p4Q2PZ37AFR_originalEffectiveHaarCells :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := Fintype.card Grid
  cell := p4Q2PZ37AFQ_cells
  hMeas := p4Q2PZ37AFQ_cells_measurable
  hPartition := p4Q2PZ37AFQ_cells_partition
  weight := p4Q2PZ37AFR_fixedWeight
  weightError := fun _ => (11 / 24 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy := p4Q2PZ37AFR_fixedWeight_accuracy

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_vertexZ_eq_real
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_vertexZ_inner_le_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_sphereGrid_inner_le_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_originalGrid_separated
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_originalCenters_separated
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_originalSmallBall_subset_cell
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_everyCell_originalHaar_ge_rational
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_everyCell_originalHaar_le_half
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_originalFiniteCenterSet_card_le_24
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_originalFiniteCenterSet_isNet
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_trueRadialHaar_fourFifths_ge_oneOver24
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_fixedWeight_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_fixedWeight_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFR_fixedWeight_accuracy
