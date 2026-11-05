import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatialHaarSignedQuadratureV5_PZ37AGC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimalMomentHaarV5_PZ37AFT
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGD — genuine spatial product of AFQ twenty-four Haar cells

AFQ proved that the ACTUAL normalized SU(2) Haar space has a measurable
first-center partition into 24 cells. AFT proved for every one-link cell
a fixed rational mass interval

  1/160000 <= Haar(C_i) <= 625/1781.

AGD builds the finite product of these SAME cells on every actual spatial
link, indexed by 24^(number of spatial links). There is one and only one
product cell per original spatial configuration. The cell is measurable
in the genuine product Haar sigma algebra; its mass equals the product
of the ACTUAL one-link Haar masses (not a surrogate probability measure).

Consequently, for L = number of original spatial links,

  (1/160000)^L <= mu_H(C_index) <= (625/1781)^L.

The rational midpoint and radius of this interval provide a completely
explicit finite original-spatial-Haar partition with mass certificates for
AGC. No numerical Wilson/transfer signed samples or nonzero transfer
signs are claimed: such pointwise local physical integrand enclosures
remain the next, independent obstruction.

All previous Lean files, physical quantities, Haar measures, pins and
the public aggregation root remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGD_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGD_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGD_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGD_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGD_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AGD_oneLinkProbability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Grid" => Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)

local instance p4Q2PZ37AGD_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGD_spatialProbability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Every actual spatial link carries its own AFQ genuine 24-cell index. -/
def p4Q2PZ37AGD_spatialGridIndex (H : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceLink H →
    Fin (Fintype.card p4Q2PZ37AFQ_GridIndex)

noncomputable instance p4Q2PZ37AGD_spatialGridFintype (H : ℕ) :
    Fintype (p4Q2PZ37AGD_spatialGridIndex H) := by
  unfold p4Q2PZ37AGD_spatialGridIndex
  infer_instance

/-- Genuine set-theoretic product rectangle in the original spatial carrier. -/
def p4Q2PZ37AGD_spatialCell
    (index : p4Q2PZ37AGD_spatialGridIndex H) : Set Cfg :=
  Set.univ.pi (fun e : Link => p4Q2PZ37AFQ_cells (index e))

/-- The original product cell is Haar-measurable. -/
theorem p4Q2PZ37AGD_spatialCell_measurable
    (index : p4Q2PZ37AGD_spatialGridIndex H) :
    MeasurableSet (p4Q2PZ37AGD_spatialCell H index) := by
  unfold p4Q2PZ37AGD_spatialCell
  exact MeasurableSet.univ_pi
    (fun e : Link => p4Q2PZ37AFQ_cells_measurable (index e))

/-- Every actual original spatial configuration lies in exactly one
product cell, since AFQ gives unique membership on each SU(2) link. -/
theorem p4Q2PZ37AGD_spatialCells_partition (A : Cfg) :
    ∃ index : p4Q2PZ37AGD_spatialGridIndex H,
      A ∈ p4Q2PZ37AGD_spatialCell H index ∧
      ∀ next : p4Q2PZ37AGD_spatialGridIndex H,
        A ∈ p4Q2PZ37AGD_spatialCell H next → next = index := by
  classical
  let index : p4Q2PZ37AGD_spatialGridIndex H :=
    fun e => Classical.choose (p4Q2PZ37AFQ_cells_partition (A e))
  have hmem (e : Link) : A e ∈ p4Q2PZ37AFQ_cells (index e) :=
    (Classical.choose_spec (p4Q2PZ37AFQ_cells_partition (A e))).1
  refine ⟨index, ?_, ?_⟩
  · change ∀ e : Link, A e ∈ p4Q2PZ37AFQ_cells (index e)
    exact hmem
  · intro next hnext
    funext e
    have he : A e ∈ p4Q2PZ37AFQ_cells (next e) := by
      exact (Set.mem_univ_pi.mp hnext) e (Set.mem_univ e)
    exact (Classical.choose_spec
      (p4Q2PZ37AFQ_cells_partition (A e))).2 (next e) he

/-- Exact genuine spatial-Haar cell mass is the product of the actual
SU(2) one-link Haar masses; no discrete replacement is introduced. -/
theorem p4Q2PZ37AGD_spatialCell_HaarMass
    (index : p4Q2PZ37AGD_spatialGridIndex H) :
    muH (p4Q2PZ37AGD_spatialCell H index) =
      ∏ e : Link, normalizedCompactHaar G
        (p4Q2PZ37AFQ_cells (index e)) := by
  unfold p4Q2PZ37AGD_spatialCell
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  exact Measure.pi_pi (fun _ : Link => normalizedCompactHaar G)
    (fun e : Link => p4Q2PZ37AFQ_cells (index e))

/-- The real-valued true Haar mass also factorizes on these rectangles. -/
theorem p4Q2PZ37AGD_spatialCell_HaarMass_real
    (index : p4Q2PZ37AGD_spatialGridIndex H) :
    Measure.real muH (p4Q2PZ37AGD_spatialCell H index) =
      ∏ e : Link, Measure.real (normalizedCompactHaar G)
        (p4Q2PZ37AFQ_cells (index e)) := by
  change (muH (p4Q2PZ37AGD_spatialCell H index)).toReal =
    ∏ e : Link,
      (normalizedCompactHaar G (p4Q2PZ37AFQ_cells (index e))).toReal
  rw [p4Q2PZ37AGD_spatialCell_HaarMass H index, ENNReal.toReal_prod]

/-- Rational lower and upper bounds determined by the literal spatial
link carrier and the certified AFT one-link Haar mass bounds. -/
def p4Q2PZ37AGD_rationalLower (H : ℕ) : ℚ :=
  (1 / 160000 : ℚ) ^ Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)

def p4Q2PZ37AGD_rationalUpper (H : ℕ) : ℚ :=
  (625 / 1781 : ℚ) ^ Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)

/-- Fully explicit finite-volume rational interval for EVERY actual
spatial product cell. -/
theorem p4Q2PZ37AGD_spatialCell_HaarMass_interval
    (index : p4Q2PZ37AGD_spatialGridIndex H) :
    ((p4Q2PZ37AGD_rationalLower H : ℚ) : ℝ) ≤
        Measure.real muH (p4Q2PZ37AGD_spatialCell H index) ∧
    Measure.real muH (p4Q2PZ37AGD_spatialCell H index) ≤
        ((p4Q2PZ37AGD_rationalUpper H : ℚ) : ℝ) := by
  rw [p4Q2PZ37AGD_spatialCell_HaarMass_real H index]
  constructor
  · change ((1 / 160000 : ℚ) ^ Fintype.card Link : ℝ) ≤
      ∏ e : Link, Measure.real (normalizedCompactHaar G)
        (p4Q2PZ37AFQ_cells (index e))
    push_cast
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (by intro e he; norm_num)
      (by intro e he; exact (p4Q2PZ37AFT_everyCell_originalHaar_interval (index e)).1)
  · change (∏ e : Link, Measure.real (normalizedCompactHaar G)
        (p4Q2PZ37AFQ_cells (index e))) ≤
      ((625 / 1781 : ℚ) ^ Fintype.card Link : ℝ)
    push_cast
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod
      (by intro e he; exact measureReal_nonneg)
      (by intro e he; exact (p4Q2PZ37AFT_everyCell_originalHaar_interval (index e)).2)

/-- The rational endpoints are ordered, also in the zero-link case. -/
theorem p4Q2PZ37AGD_rationalLower_le_upper :
    p4Q2PZ37AGD_rationalLower H ≤
      p4Q2PZ37AGD_rationalUpper H := by
  unfold p4Q2PZ37AGD_rationalLower p4Q2PZ37AGD_rationalUpper
  gcongr
  norm_num

/-- Use the exact finite equivalence rather than pretending the spatial
index is a single SU(2) link; the index has 24^L elements. -/
noncomputable def p4Q2PZ37AGD_indexFromFin (H : ℕ)
    (i : Fin (Fintype.card (p4Q2PZ37AGD_spatialGridIndex H))) :
    p4Q2PZ37AGD_spatialGridIndex H :=
  (Fintype.equivFin (p4Q2PZ37AGD_spatialGridIndex H)).symm i

/-- Genuine original spatial-Haar finite cell partition presented in the
exact Fin-indexed type required by AGC. -/
noncomputable def p4Q2PZ37AGD_toAGCOriginalHaarCells :
    p4Q2PZ37AGC_originalHaarCells H where
  n := Fintype.card (p4Q2PZ37AGD_spatialGridIndex H)
  cell := fun i => p4Q2PZ37AGD_spatialCell H (p4Q2PZ37AGD_indexFromFin H i)
  hMeas := by
    intro i
    exact p4Q2PZ37AGD_spatialCell_measurable H _
  hPartition := by
    intro A
    obtain ⟨index, hindex, hOnly⟩ := p4Q2PZ37AGD_spatialCells_partition H A
    let equiv := Fintype.equivFin (p4Q2PZ37AGD_spatialGridIndex H)
    refine ⟨equiv index, ?_, ?_⟩
    · simpa [p4Q2PZ37AGD_indexFromFin, equiv] using hindex
    · intro j hj
      apply equiv.symm.injective
      have hj' : A ∈ p4Q2PZ37AGD_spatialCell H (equiv.symm j) := by
        simpa only [p4Q2PZ37AGD_indexFromFin, equiv] using hj
      simpa using hOnly (equiv.symm j) hj'
  weight := fun _ =>
    (p4Q2PZ37AGD_rationalLower H + p4Q2PZ37AGD_rationalUpper H) / 2
  weightError := fun _ =>
    (((p4Q2PZ37AGD_rationalUpper H -
        p4Q2PZ37AGD_rationalLower H) / 2 : ℚ) : ℝ)
  hWeightError_nonneg := by
    intro i
    exact_mod_cast
      (div_nonneg (sub_nonneg.mpr
        (p4Q2PZ37AGD_rationalLower_le_upper H)) (by norm_num : (0:ℚ) ≤ 2))
  hWeightAccuracy := by
    intro i
    obtain ⟨hLow, hHigh⟩ := p4Q2PZ37AGD_spatialCell_HaarMass_interval H
      (p4Q2PZ37AGD_indexFromFin H i)
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_sub]
    apply abs_le.mpr
    constructor <;> linarith only [hLow,hHigh]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_spatialCell_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_spatialCells_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_spatialCell_HaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_spatialCell_HaarMass_real
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_spatialCell_HaarMass_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_rationalLower_le_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGD_toAGCOriginalHaarCells
