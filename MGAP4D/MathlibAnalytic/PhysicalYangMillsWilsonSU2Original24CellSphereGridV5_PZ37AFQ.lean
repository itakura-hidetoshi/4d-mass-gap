import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalEightQuaternionChordalCellV5_PZ37AFP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereChordalIsometryV5_PZ37ADT
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFQ — genuine original SU(2) twenty-four-cell spherical grid

This append-only proof uses exactly the original ADR/ADS/ADT
SU(2) <-> S³ maps and the true ADK Wilson J-chord.
The finite grid consists of the 8 signed coordinate axes and 16
signed half-diagonals in the ACTUAL four-real-coordinate unit sphere.

For every sphere point, either some |x_j| >= 7/10 or the l1
coordinate sum is at least 7/5. Consequently one of these 24
centers has inner product >= 7/10, and original J-chord square
<= 3/5 < (4/5)^2. We obtain OPEN radius 4/5, strictly below 1.

The Haar cells are AFN first-center measurable cells for the same
normalized original SU(2) Haar. The tighter rational error 1/64
is a genuine (NONCOMPUTABLE) rational-density enclosure depending
on unknown Haar cell masses; it is NOT an explicit evaluated weight
table or a numerical quadrature algorithm. This is deliberately
distinguished from AFP's fixed positive 1/8 weights.

The original physical signed FF receiver, its square, four mode
products, AFG independent boundary shell table and AFM->AFI
certificate remain unchanged, with literal zero samples and the
unchanged true receiver norm envelopes. No true strict threshold
crossing, H-uniform coercivity, spectral gap or continuum mass gap
is implied.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "Φ" => p4Q2PZ37ADR_originalSU2ToSphere
local notation "Ψ" => p4Q2PZ37ADS_originalSphereToSU2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "mu" => normalizedCompactHaar G

local instance p4Q2PZ37AFQ_topological : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFQ_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The eight signed real coordinate-axis vectors. -/
def p4Q2PZ37AFQ_axisVector (j : Fin 4) (s : Bool) : E4 :=
  WithLp.toLp 2 (fun k : Fin 4 =>
    if k = j then (if s then (-1 : ℝ) else 1) else 0)

/-- The sixteen half-diagonals; each has Euclidean norm one. -/
def p4Q2PZ37AFQ_diagVector (s : Fin 4 → Bool) : E4 :=
  WithLp.toLp 2 (fun k : Fin 4 =>
    if s k then (-1 / 2 : ℝ) else (1 / 2 : ℝ))

theorem p4Q2PZ37AFQ_axis_norm_sq_one (j : Fin 4) (s : Bool) :
    ‖p4Q2PZ37AFQ_axisVector j s‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases j <;> cases s <;>
    norm_num [p4Q2PZ37AFQ_axisVector, Fin.sum_univ_four]

theorem p4Q2PZ37AFQ_diag_norm_sq_one (s : Fin 4 → Bool) :
    ‖p4Q2PZ37AFQ_diagVector s‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hSq (k : Fin 4) :
      (p4Q2PZ37AFQ_diagVector s k) ^ 2 = (1 / 4 : ℝ) := by
    by_cases hk : s k <;>
      simp [p4Q2PZ37AFQ_diagVector, hk] <;> norm_num
  simp only [Fin.sum_univ_four]
  rw [hSq 0, hSq 1, hSq 2, hSq 3]
  norm_num

/-- Each of the 8 axes lies in the genuine unit S³. -/
def p4Q2PZ37AFQ_axisSphere (j : Fin 4) (s : Bool) : S3 :=
  ⟨p4Q2PZ37AFQ_axisVector j s, by
    change dist (p4Q2PZ37AFQ_axisVector j s) (0 : E4) = 1
    rw [dist_zero_right]
    have hs := p4Q2PZ37AFQ_axis_norm_sq_one j s
    have h0 := norm_nonneg (p4Q2PZ37AFQ_axisVector j s)
    nlinarith⟩

/-- Each of the 16 half-diagonals lies in the genuine unit S³. -/
def p4Q2PZ37AFQ_diagSphere (s : Fin 4 → Bool) : S3 :=
  ⟨p4Q2PZ37AFQ_diagVector s, by
    change dist (p4Q2PZ37AFQ_diagVector s) (0 : E4) = 1
    rw [dist_zero_right]
    have hs := p4Q2PZ37AFQ_diag_norm_sq_one s
    have h0 := norm_nonneg (p4Q2PZ37AFQ_diagVector s)
    nlinarith⟩

/-- Named finite 24-vertex four-coordinate grid. -/
abbrev p4Q2PZ37AFQ_GridIndex :=
  Sum (Fin 4 × Bool) (Fin 4 → Bool)

theorem p4Q2PZ37AFQ_gridIndex_card :
    Fintype.card p4Q2PZ37AFQ_GridIndex = 24 := by
  norm_num [p4Q2PZ37AFQ_GridIndex, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fun]

def p4Q2PZ37AFQ_sphereGridCenter (i : p4Q2PZ37AFQ_GridIndex) : S3 :=
  match i with
  | Sum.inl (j, s) => p4Q2PZ37AFQ_axisSphere j s
  | Sum.inr s => p4Q2PZ37AFQ_diagSphere s

theorem p4Q2PZ37AFQ_inner_axis
    (x : E4) (j : Fin 4) (s : Bool) :
    inner ℝ x (p4Q2PZ37AFQ_axisVector j s) =
      x j * (if s then (-1 : ℝ) else 1) := by
  fin_cases j <;> cases s <;>
    simp [p4Q2PZ37AFQ_axisVector, PiLp.inner_apply,
      Fin.sum_univ_four, realScalarInner_eq_mul]

theorem p4Q2PZ37AFQ_inner_diag
    (x : E4) (s : Fin 4 → Bool) :
    inner ℝ x (p4Q2PZ37AFQ_diagVector s) =
      ∑ k : Fin 4, x k * (if s k then (-1 / 2 : ℝ) else 1 / 2) := by
  simp [p4Q2PZ37AFQ_diagVector, PiLp.inner_apply,
    realScalarInner_eq_mul]

/-- Deterministic signs matching the actual four real coordinates. -/
def p4Q2PZ37AFQ_matchingSigns (x : E4) : Fin 4 → Bool :=
  fun k => decide (x k < 0)

theorem p4Q2PZ37AFQ_inner_matching_diag (x : E4) :
    inner ℝ x (p4Q2PZ37AFQ_diagVector (p4Q2PZ37AFQ_matchingSigns x)) =
      (∑ k : Fin 4, |x k|) / 2 := by
  rw [p4Q2PZ37AFQ_inner_diag]
  have hTerm (k : Fin 4) :
      x k * (if p4Q2PZ37AFQ_matchingSigns x k
        then (-1 / 2 : ℝ) else 1 / 2) = |x k| / 2 := by
    by_cases hk : x k < 0
    · simp [p4Q2PZ37AFQ_matchingSigns, hk, abs_of_neg hk]
      ring
    · have hnonneg : 0 ≤ x k := le_of_not_gt hk
      simp [p4Q2PZ37AFQ_matchingSigns, hk, abs_of_nonneg hnonneg]
      ring
  simp only [Fin.sum_univ_four]
  rw [hTerm 0, hTerm 1, hTerm 2, hTerm 3]
  ring

/-- Real-four coordinate pigeonhole with quantitative 7/10 margin.
If every |x_j| < 7/10, the unit norm forces l1 >= 10/7 > 7/5. -/
theorem p4Q2PZ37AFQ_axis_or_diag
    (x : E4) (hx : ‖x‖ ^ 2 = 1) :
    (∃ j : Fin 4, (7 / 10 : ℝ) ≤ |x j|) ∨
      (7 / 5 : ℝ) ≤ ∑ j : Fin 4, |x j| := by
  by_cases hAxis : ∃ j : Fin 4, (7 / 10 : ℝ) ≤ |x j|
  · exact Or.inl hAxis
  · right
    have hSmall (j : Fin 4) : |x j| ≤ (7 / 10 : ℝ) :=
      le_of_lt (lt_of_not_ge (fun hj => hAxis ⟨j, hj⟩))
    have hEach (j : Fin 4) :
        (x j) ^ 2 ≤ (7 / 10 : ℝ) * |x j| := by
      have hMul : 0 ≤ |x j| * ((7 / 10 : ℝ) - |x j|) :=
        mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (hSmall j))
      nlinarith only [hMul, sq_abs (x j)]
    have hSum : (∑ j : Fin 4, (x j) ^ 2) = 1 := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using hx
    simp only [Fin.sum_univ_four] at hSum ⊢
    have h0 := hEach 0
    have h1 := hEach 1
    have h2 := hEach 2
    have h3 := hEach 3
    nlinarith only [hSum, h0, h1, h2, h3]

/-- Exact 24-vertex spherical inner-product covering certificate. -/
theorem p4Q2PZ37AFQ_sphereGrid_innerCover (x : S3) :
    ∃ i : p4Q2PZ37AFQ_GridIndex,
      (7 / 10 : ℝ) ≤
        inner ℝ (x : E4) (p4Q2PZ37AFQ_sphereGridCenter i : E4) := by
  have hxNorm : ‖(x : E4)‖ = 1 := by
    have hSphere : dist (x : E4) (0 : E4) = 1 := x.property
    simpa only [dist_zero_right] using hSphere
  have hxSq : ‖(x : E4)‖ ^ 2 = 1 := by
    rw [hxNorm]
    norm_num
  rcases p4Q2PZ37AFQ_axis_or_diag (x : E4) hxSq with
    ⟨j, hj⟩ | hsum
  · by_cases hsign : 0 ≤ (x : E4) j
    · refine ⟨Sum.inl (j, false), ?_⟩
      change (7 / 10 : ℝ) ≤
        inner ℝ (x : E4) (p4Q2PZ37AFQ_axisVector j false)
      rw [p4Q2PZ37AFQ_inner_axis]
      simpa [abs_of_nonneg hsign] using hj
    · have hneg : (x : E4) j < 0 := lt_of_not_ge hsign
      refine ⟨Sum.inl (j, true), ?_⟩
      change (7 / 10 : ℝ) ≤
        inner ℝ (x : E4) (p4Q2PZ37AFQ_axisVector j true)
      rw [p4Q2PZ37AFQ_inner_axis]
      simpa [abs_of_neg hneg] using hj
  · refine ⟨Sum.inr (p4Q2PZ37AFQ_matchingSigns (x : E4)), ?_⟩
    change (7 / 10 : ℝ) ≤
      inner ℝ (x : E4)
        (p4Q2PZ37AFQ_diagVector (p4Q2PZ37AFQ_matchingSigns (x : E4)))
    rw [p4Q2PZ37AFQ_inner_matching_diag]
    linarith

/-- A fixed enumeration of exactly 24 EXPLICIT original sphere points. -/
noncomputable def p4Q2PZ37AFQ_sphereCenters
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) : S3 :=
  p4Q2PZ37AFQ_sphereGridCenter
    ((Fintype.equivFin p4Q2PZ37AFQ_GridIndex).symm i)

/-- The same 24 points transported into actual original SU(2) matrices. -/
noncomputable def p4Q2PZ37AFQ_originalCenters
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) : G :=
  Ψ (p4Q2PZ37AFQ_sphereCenters i)

/-- Every genuine SU(2) point is in one of the 24 OPEN 4/5-balls. -/
theorem p4Q2PZ37AFQ_originalCenters_openCover (g : G) :
    ∃ i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex),
      g ∈ BallJ (p4Q2PZ37AFQ_originalCenters i) (4 / 5) := by
  obtain ⟨a, ha⟩ := p4Q2PZ37AFQ_sphereGrid_innerCover (Φ g)
  let i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex) :=
    (Fintype.equivFin p4Q2PZ37AFQ_GridIndex) a
  have hc : p4Q2PZ37AFQ_sphereCenters i =
      p4Q2PZ37AFQ_sphereGridCenter a := by
    simp [p4Q2PZ37AFQ_sphereCenters, i]
  have hV : V (p4Q2PZ37AFQ_originalCenters i) =
      (p4Q2PZ37AFQ_sphereGridCenter a : E4) := by
    change V (Ψ (p4Q2PZ37AFQ_sphereCenters i)) =
      (p4Q2PZ37AFQ_sphereGridCenter a : E4)
    rw [hc]
    simpa only [p4Q2PZ37ADR_originalSU2ToSphere] using
      (congrArg Subtype.val
        (p4Q2PZ37ADS_sphere_roundtrip
          (p4Q2PZ37AFQ_sphereGridCenter a)))
  have hInner : (7 / 10 : ℝ) ≤
      inner ℝ (V g) (V (p4Q2PZ37AFQ_originalCenters i)) := by
    rw [hV]
    exact ha
  have hSq : (dJ g (p4Q2PZ37AFQ_originalCenters i)) ^ 2 =
      2 - 2 * inner ℝ (V g) (V (p4Q2PZ37AFQ_originalCenters i)) := by
    rw [p4Q2PZ37ADT_originalChordal_sq_eq_sphereChord_sq,
      norm_sub_sq_real,
      p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one,
      p4Q2PZ37ADR_originalFourCoordinates_norm_sq_one]
    ring
  have hNN : 0 ≤ dJ g (p4Q2PZ37AFQ_originalCenters i) :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg _ _
  have hLt : dJ g (p4Q2PZ37AFQ_originalCenters i) < (4 / 5 : ℝ) := by
    nlinarith only [hInner, hSq, hNN]
  refine ⟨i, ?_⟩
  change dJ (p4Q2PZ37AFQ_originalCenters i) g < (4 / 5 : ℝ)
  rw [p4Q2PZ37ADK_trueChordalDistance_symm]
  exact hLt

/-- Fixed 24-center FIRST-index Borel cells on the ORIGINAL Haar space. -/
def p4Q2PZ37AFQ_cells
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) : Set G :=
  p4Q2PZ37AFN_originalFirstCenterCell
    (Fintype.card p4Q2PZ37AFQ_GridIndex)
    p4Q2PZ37AFQ_originalCenters (4 / 5) i

theorem p4Q2PZ37AFQ_cells_measurable
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) :
    MeasurableSet (p4Q2PZ37AFQ_cells i) :=
  p4Q2PZ37AFN_originalFirstCenterCell_measurable _ _ _ _

theorem p4Q2PZ37AFQ_cells_partition :
    ∀ g : G, ∃ i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex),
      g ∈ p4Q2PZ37AFQ_cells i ∧
      ∀ j : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex),
        g ∈ p4Q2PZ37AFQ_cells j → j = i :=
  p4Q2PZ37AFN_originalFirstCenterCell_partition
    (Fintype.card p4Q2PZ37AFQ_GridIndex)
    p4Q2PZ37AFQ_originalCenters (4 / 5)
    p4Q2PZ37AFQ_originalCenters_openCover

theorem p4Q2PZ37AFQ_cells_chordalRadius
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) (g : G)
    (hg : g ∈ p4Q2PZ37AFQ_cells i) :
    dJ g (p4Q2PZ37AFQ_originalCenters i) ≤ (4 / 5 : ℝ) := by
  have hb : g ∈ BallJ (p4Q2PZ37AFQ_originalCenters i) (4 / 5) :=
    (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      (Fintype.card p4Q2PZ37AFQ_GridIndex)
      p4Q2PZ37AFQ_originalCenters (4 / 5) i g).1 hg |>.1
  calc
    dJ g (p4Q2PZ37AFQ_originalCenters i) =
        dJ (p4Q2PZ37AFQ_originalCenters i) g :=
      p4Q2PZ37ADK_trueChordalDistance_symm _ _
    _ ≤ 4 / 5 := le_of_lt hb

/-- Rational enclosure from AFN. The returned rational depends on
the unknown ACTUAL Haar mass; it is NOT a computed quadrature. -/
noncomputable def p4Q2PZ37AFQ_rationalWeight
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) : ℚ :=
  p4Q2PZ37AFN_rationalEnclosure
    (Measure.real mu (p4Q2PZ37AFQ_cells i))
    (1 / 64) (by norm_num)

theorem p4Q2PZ37AFQ_rationalMass_accuracy
    (i : Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)) :
    |Measure.real mu (p4Q2PZ37AFQ_cells i) -
      (p4Q2PZ37AFQ_rationalWeight i : ℝ)| ≤ (1 / 64 : ℝ) :=
  p4Q2PZ37AFN_rationalEnclosure_error
    (Measure.real mu (p4Q2PZ37AFQ_cells i))
    (1 / 64) (by norm_num)

/-- Honest true-Haar 24-cell AFJ partition with 1/64 rational
enclosure existence, NOT certified computed cell mass values. -/
noncomputable def p4Q2PZ37AFQ_originalHaarCells :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := Fintype.card p4Q2PZ37AFQ_GridIndex
  cell := p4Q2PZ37AFQ_cells
  hMeas := p4Q2PZ37AFQ_cells_measurable
  hPartition := p4Q2PZ37AFQ_cells_partition
  weight := p4Q2PZ37AFQ_rationalWeight
  weightError := fun _ => (1 / 64 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy := p4Q2PZ37AFQ_rationalMass_accuracy

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

local instance p4Q2PZ37AFQ_links : Fintype Link := Fintype.ofFinite _

/-- Fixed radius 4/5 and 24 true SU(2) centers in the unchanged
original FF BCF receiver, using honest norm-controlled zero samples.
The Haar rational weights are noncomputable; no numeric sample
evaluation or strict shell crossing is claimed. -/
noncomputable def p4Q2PZ37AFQ_original24CellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c where
  partition := p4Q2PZ37AFQ_originalHaarCells
  center := p4Q2PZ37AFQ_originalCenters
  radius := 4 / 5
  hRadius := by norm_num
  hCellRadius := p4Q2PZ37AFQ_cells_chordalRadius
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
        H e a (p4Q2PZ37AFQ_originalCenters i))
  secondSample := fun _ _ => 0
  secondSampleError := fun _ => (MFF e) ^ 2
  hSecondSampleError_nonneg := by
    intro a ha
    exact sq_nonneg _
  hSecondSample := by
    intro a ha i
    have hBound := p4Q2PZ37AFO_originalFF_square_le_normSquare
      H e a (p4Q2PZ37AFQ_originalCenters i)
    have hSq : 0 ≤ (F e a (p4Q2PZ37AFQ_originalCenters i)) ^ 2 :=
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
        H e a j (p4Q2PZ37AFQ_originalCenters i))

theorem p4Q2PZ37AFQ_original24Cell_radius
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    (p4Q2PZ37AFQ_original24CellSamples H e c hlo).radius =
      (4 / 5 : ℝ) := rfl

/-- The SAME original physical AFM->AFI certificate, now on the
verified 24-center S³ grid, with no strengthened physical premise. -/
noncomputable def p4Q2PZ37AFQ_trueCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    H e c (p4Q2PZ37AFQ_original24CellSamples H e c hlo)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_axis_norm_sq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_diag_norm_sq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_gridIndex_card
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_inner_matching_diag
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_axis_or_diag
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_sphereGrid_innerCover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_originalCenters_openCover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_cells_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_cells_partition
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_cells_chordalRadius
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFQ_rationalMass_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFQ_original24Cell_radius
