import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteBorelHaarCellExistenceV5_PZ37AFN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoRadiusAntipodalHaarObstructionV5_PZ37ADO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFO — explicit ORIGINAL SU(2) antipodal two-cell Haar certificate

AFN proved noncomputable existence of arbitrary-radius genuine Haar
cells and rational weights/samples. AFO constructs an ACTUAL fixed
two-cell coarse certificate with NO rational choice oracle.

The original ADK SU(2) Wilson-feature balls at the identity and
the genuine central antipode z = -1, both of radius 3/2, cover SU(2).
The first cell is B_J(1,3/2); the second is its complement, which
is contained in B_J(z,3/2). Both are genuine Borel subsets of the
unchanged normalized SU(2) Haar space.

From ADN/ADO, true Haar(B_J(1,3/2)) lies in [1/2, 7/8].
The actual Haar masses of the two cells thus admit EXPLICIT
rational weights 11/16, 5/16 with errors 3/16 each.
Both weights are positive, sum to exactly one and require no
real-valued Haar oracle, classical irrational approximation choice,
or independent numerical mass premise.

For the ORIGINAL signed FF Wilson/Perron receiver, all finite
center samples may be chosen as the literal rational 0.
Their rigorously proved, though coarse, errors are the same
genuine FF BCF norm M_FF, M_FF², M_FF. This makes a fully
specified AFM input certificate (given the independent AFG
boundary sample table c and nonnegative lower threshold).

This is an effective *analytic coarse baseline*, not a small-radius
grid, narrow certified Haar mass computation, nonempty crossing,
volume-uniform physical coercivity, spectral gap, or continuum
Yang--Mills mass gap. Source/measure/transfer/pins remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "z" => p4Q2PZ35D4_centralMinusOne

local instance p4Q2PZ37AFO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFO_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFO_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFO_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFO_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFO_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The explicit original SU(2) physical centers are 1 and the
genuine central antipode. No infinite net or selected centers. -/
def p4Q2PZ37AFO_twoCenters (i : Fin 2) : G :=
  if i = 0 then 1 else z

/-- Exact disjoint genuine two-cell partition: first ball and
its actual Borel complement, not a replacement finite Haar law. -/
def p4Q2PZ37AFO_twoCells (i : Fin 2) : Set G :=
  if i = 0 then BallJ (1 : G) (3 / 2)
  else (BallJ (1 : G) (3 / 2))ᶜ

theorem p4Q2PZ37AFO_twoCells_measurable (i : Fin 2) :
    MeasurableSet (p4Q2PZ37AFO_twoCells i) := by
  by_cases hi : i = 0
  · simpa [p4Q2PZ37AFO_twoCells, hi] using
      (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) (3 / 2)).measurableSet
  · simpa [p4Q2PZ37AFO_twoCells, hi] using
      (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) (3 / 2)).measurableSet.compl

theorem p4Q2PZ37AFO_twoCells_partition :
    ∀ g : G, ∃ i : Fin 2,
      g ∈ p4Q2PZ37AFO_twoCells i ∧
      ∀ j : Fin 2, g ∈ p4Q2PZ37AFO_twoCells j → j = i := by
  intro g
  by_cases hg : g ∈ BallJ (1 : G) (3 / 2)
  · refine ⟨0, ?_, ?_⟩
    · simpa [p4Q2PZ37AFO_twoCells] using hg
    · intro j hj
      fin_cases j
      · rfl
      · exfalso
        have hnot : g ∉ BallJ (1 : G) (3 / 2) := by
          simpa [p4Q2PZ37AFO_twoCells] using hj
        exact hnot hg
  · refine ⟨1, ?_, ?_⟩
    · simpa [p4Q2PZ37AFO_twoCells] using hg
    · intro j hj
      fin_cases j
      · exfalso
        have hyes : g ∈ BallJ (1 : G) (3 / 2) := by
          simpa [p4Q2PZ37AFO_twoCells] using hj
        exact hg hyes
      · rfl

/-- Genuine two antipodal radius-3/2 balls already cover original SU(2). -/
theorem p4Q2PZ37AFO_twoAntipodalBalls_cover :
    BallJ (1 : G) (3 / 2) ∪ BallJ z (3 / 2) = Set.univ :=
  p4Q2PZ37ADN_antipodalBalls_cover
    (3 / 2) (by norm_num) (by norm_num)

/-- Each EXPLICIT Borel cell lies inside the ADK original
radius-3/2 chordal ball at its actual two finite centers. -/
theorem p4Q2PZ37AFO_twoCells_chordalRadius
    (i : Fin 2) (g : G)
    (hg : g ∈ p4Q2PZ37AFO_twoCells i) :
    dJ g (p4Q2PZ37AFO_twoCenters i) ≤ (3 / 2 : ℝ) := by
  by_cases hi : i = 0
  · have hg0 : g ∈ BallJ (1 : G) (3 / 2) := by
      simpa [p4Q2PZ37AFO_twoCells, hi] using hg
    have hd : dJ (1 : G) g ≤ (3 / 2 : ℝ) := le_of_lt hg0
    calc
      dJ g (p4Q2PZ37AFO_twoCenters i) =
          dJ (1 : G) g := by
            rw [p4Q2PZ37ADK_trueChordalDistance_symm]
            simp [p4Q2PZ37AFO_twoCenters, hi]
      _ ≤ 3 / 2 := hd
  · have hg0 : g ∉ BallJ (1 : G) (3 / 2) := by
      simpa [p4Q2PZ37AFO_twoCells, hi] using hg
    have hUnion : g ∈ BallJ (1 : G) (3 / 2) ∪ BallJ z (3 / 2) := by
      rw [p4Q2PZ37AFO_twoAntipodalBalls_cover]
      trivial
    have hgz : g ∈ BallJ z (3 / 2) :=
      hUnion.resolve_left hg0
    have hd : dJ z g ≤ (3 / 2 : ℝ) := le_of_lt hgz
    calc
      dJ g (p4Q2PZ37AFO_twoCenters i) = dJ z g := by
        rw [p4Q2PZ37ADK_trueChordalDistance_symm]
        simp [p4Q2PZ37AFO_twoCenters, hi]
      _ ≤ 3 / 2 := hd

/-- The genuine first antipodal cell has exact ADO-derived
true-Haar mass range [1/2,7/8]. -/
theorem p4Q2PZ37AFO_firstCell_originalHaar_interval :
    (1 / 2 : ℝ) ≤ Measure.real mu (p4Q2PZ37AFO_twoCells 0) ∧
    Measure.real mu (p4Q2PZ37AFO_twoCells 0) ≤ (7 / 8 : ℝ) := by
  simpa [p4Q2PZ37AFO_twoCells,
    p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass] using
    p4Q2PZ37ADO_radialMass_threeHalves_interval

/-- The two genuine Haar cell masses sum to exactly ONE,
without estimating, discretizing or changing the Haar law. -/
theorem p4Q2PZ37AFO_twoCellHaarMass_sum_one :
    Measure.real mu (p4Q2PZ37AFO_twoCells 0) +
      Measure.real mu (p4Q2PZ37AFO_twoCells 1) = 1 := by
  have h := measureReal_add_measureReal_compl (μ := mu)
    (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) (3 / 2)).measurableSet
  simpa [p4Q2PZ37AFO_twoCells] using h

/-- An exact, fully specified, rational two-weight vector. -/
def p4Q2PZ37AFO_twoHaarRationalWeight (i : Fin 2) : ℚ :=
  if i = 0 then 11 / 16 else 5 / 16

theorem p4Q2PZ37AFO_twoHaarRationalWeight_sum_one :
    (∑ i : Fin 2, p4Q2PZ37AFO_twoHaarRationalWeight i) = (1 : ℚ) := by
  norm_num [Fin.sum_univ_two, p4Q2PZ37AFO_twoHaarRationalWeight]

theorem p4Q2PZ37AFO_twoHaarRationalWeight_positive (i : Fin 2) :
    0 < p4Q2PZ37AFO_twoHaarRationalWeight i := by
  fin_cases i <;> norm_num [p4Q2PZ37AFO_twoHaarRationalWeight]

/-- Explicit rational masses need NO Classical.choose.
Both true Haar masses differ from [11/16,5/16] by at most 3/16. -/
theorem p4Q2PZ37AFO_twoCellHaarRational_accuracy
    (i : Fin 2) :
    |Measure.real mu (p4Q2PZ37AFO_twoCells i) -
      (p4Q2PZ37AFO_twoHaarRationalWeight i : ℝ)| ≤ (3 / 16 : ℝ) := by
  have hFirst := p4Q2PZ37AFO_firstCell_originalHaar_interval
  have hSum := p4Q2PZ37AFO_twoCellHaarMass_sum_one
  by_cases hi : i = 0
  · subst i
    have hw :
        (p4Q2PZ37AFO_twoHaarRationalWeight (0 : Fin 2) : ℝ) =
          (11 / 16 : ℝ) := by
      norm_num [p4Q2PZ37AFO_twoHaarRationalWeight]
    rw [hw]
    exact abs_le.mpr
      ⟨by linarith [hFirst.1], by linarith [hFirst.2]⟩
  · have hiOne : i = (1 : Fin 2) := by
      fin_cases i
      · exact False.elim (hi rfl)
      · rfl
    subst i
    have hw :
        (p4Q2PZ37AFO_twoHaarRationalWeight (1 : Fin 2) : ℝ) =
          (5 / 16 : ℝ) := by
      norm_num [p4Q2PZ37AFO_twoHaarRationalWeight]
    rw [hw]
    exact abs_le.mpr
      ⟨by linarith [hFirst.2, hSum], by linarith [hFirst.1, hSum]⟩

/-- A FIXED two-cell normalized SU(2) Haar quadrature partition:
center set and BOTH rational weights are written explicitly, and
mass tolerance 3/16 is PROVED from genuine original Haar bounds. -/
def p4Q2PZ37AFO_explicitTwoHaarCells :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := 2
  cell := p4Q2PZ37AFO_twoCells
  hMeas := p4Q2PZ37AFO_twoCells_measurable
  hPartition := p4Q2PZ37AFO_twoCells_partition
  weight := p4Q2PZ37AFO_twoHaarRationalWeight
  weightError := fun _ => (3 / 16 : ℝ)
  hWeightError_nonneg := by intro i; norm_num
  hWeightAccuracy := p4Q2PZ37AFO_twoCellHaarRational_accuracy

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

local instance p4Q2PZ37AFO_links : Fintype Link := Fintype.ofFinite _

/-- Original FF receiver square has a fully certified pointwise
bound by the SQUARE of its actual original BCF norm. -/
theorem p4Q2PZ37AFO_originalFF_square_le_normSquare
    (e : Link) (a : Pair) (g : G) :
    (F e a g) ^ 2 ≤ (MFF e) ^ 2 := by
  have hBound := p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm H e a g
  have hProduct : 0 ≤ (MFF e - |F e a g|) * (MFF e + |F e a g|) :=
    mul_nonneg (sub_nonneg.mpr hBound)
      (add_nonneg (p4Q2PZ37AFM_originalFFEnvelope_nonneg H e)
        (abs_nonneg _))
  nlinarith [sq_abs (F e a g)]

/-- Original FF times a genuine Quaternion Haar character has
a certified pointwise bound by the SAME original FF norm. -/
theorem p4Q2PZ37AFO_originalFF_character_abs_le_norm
    (e : Link) (a : Pair) (j : Fin 4) (g : G) :
    |F e a g * phi j g| ≤ MFF e := by
  have hf := p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm H e a g
  have hj := p4Q2PZ37AFL_originalFourMode_abs_le_one j g
  calc
    |F e a g * phi j g| = |F e a g| * |phi j g| := abs_mul _ _
    _ ≤ |F e a g| * 1 :=
      mul_le_mul_of_nonneg_left hj (abs_nonneg _)
    _ = |F e a g| := by ring
    _ ≤ MFF e := hf

/-- A fully EXPLICIT rational sample table, all coefficients exactly
zero, no Classical.choose. It has honest, possibly large, true
physical FF BCF-derived error bounds, and exact 2 Haar cells. -/
def p4Q2PZ37AFO_explicitPhysicalTwoCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c where
  partition := p4Q2PZ37AFO_explicitTwoHaarCells
  center := p4Q2PZ37AFO_twoCenters
  radius := 3 / 2
  hRadius := by norm_num
  hCellRadius := p4Q2PZ37AFO_twoCells_chordalRadius
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
        H e a (p4Q2PZ37AFO_twoCenters i))
  secondSample := fun _ _ => 0
  secondSampleError := fun _ => (MFF e) ^ 2
  hSecondSampleError_nonneg := by
    intro a ha
    exact sq_nonneg _
  hSecondSample := by
    intro a ha i
    have hBound := p4Q2PZ37AFO_originalFF_square_le_normSquare
      H e a (p4Q2PZ37AFO_twoCenters i)
    have hAbs :
        |(F e a (p4Q2PZ37AFO_twoCenters i)) ^ 2| =
          (F e a (p4Q2PZ37AFO_twoCenters i)) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    simpa only [Rat.cast_zero, sub_zero, hAbs] using hBound
  coefficientSample := fun _ _ _ => 0
  coefficientSampleError := fun _ _ => MFF e
  hCoefficientSampleError_nonneg := by
    intro a ha j
    exact p4Q2PZ37AFM_originalFFEnvelope_nonneg H e
  hCoefficientSample := by
    intro a ha j i
    simpa only [Rat.cast_zero, sub_zero] using
      (p4Q2PZ37AFO_originalFF_character_abs_le_norm
        H e a j (p4Q2PZ37AFO_twoCenters i))

/-- The AFO original two-cell certificate has literal finite
radius, weights, and zero rational samples; only the true physical
FF BCF norm remains in the proved interval errors. -/
theorem p4Q2PZ37AFO_originalTwoCell_certificate_radius
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    (p4Q2PZ37AFO_explicitPhysicalTwoCellSamples H e c hlo).radius =
      (3 / 2 : ℝ) := rfl

/-- Construct the exact existing AFM -> AFL -> AFK -> AFJ -> AFI
true physical coefficient and variance certificate from fixed
rational data, NOT a new virtual Haar or virtual receiver.
The independent AFG input c is retained. -/
def p4Q2PZ37AFO_explicitTrueCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    H e c (p4Q2PZ37AFO_explicitPhysicalTwoCellSamples H e c hlo)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoCells_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoCells_partition
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoAntipodalBalls_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoCells_chordalRadius
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_firstCell_originalHaar_interval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoCellHaarMass_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoHaarRationalWeight_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoHaarRationalWeight_positive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFO_twoCellHaarRational_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFO_originalFF_square_le_normSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFO_originalFF_character_abs_le_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFO_originalTwoCell_certificate_radius
