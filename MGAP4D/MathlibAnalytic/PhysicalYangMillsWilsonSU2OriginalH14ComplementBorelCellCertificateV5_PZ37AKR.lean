import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH14WeightedHaarMassThresholdV5_PZ37AKQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKR: finite Borel-cell certification interface at genuine H=14

The original finite SU(2) Wilson action, beta0=log(3/2)/64, signed ZW
source, normalized physical transfer, original negative margin, product
Haar probability, full-top projection and original AJA strict budget are
never replaced or modified.

AIT, AIB and AIW already imply an unconditional genuine H14 LOWER Haar
mass bound r14 >= 1/2. This is NOT the upper bound needed by AKQ.

For a future rigorous upper bound, independently certified disjoint Borel
cells must be on the ORIGINAL complement {u14 >= -m14}. This leaf
proves a precise finite rational certificate descent:
  * measurable disjoint cells and valid rational Haar mass lower bounds,
  * rational pointwise transfer floors at every point of each cell,
  * floors above the UNCHANGED original negative margin,
yield the true original negative-region Haar mass upper bound
  r14 <= 1 - sum_i massLower_i.
If the certified sum is at least 1-4*exp(-beta0^2*81000/2),
AKQ excludes an original finite-power AJA strict witness.

No specific H14 cells, interval computations, numerical mass bounds,
new physical source/measure or unconditional H14 witness/no-witness
are claimed. A separate numerical/interval certification remains OPEN.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- Finite, mutually disjoint Borel cells lying in the complementary
event cannot conceal any portion of the true negative-event measure.
Rational cell mass lower bounds add without assuming any numerical data.
This statement uses the original probability measure, not a discretized
replacement. -/
theorem real_probability_finite_complement_cells_budget_akr
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (negative : Set α) (hNegative : MeasurableSet negative)
    {n : ℕ} (cells : Fin n → Set α)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (Disjoint on cells))
    (hOutside : ∀ i, cells i ⊆ negativeᶜ)
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ μ.real (cells i)) :
    μ.real negative + (∑ i, (massLower i : ℝ)) ≤ 1 := by
  have hUsubset : (⋃ i, cells i) ⊆ negativeᶜ := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hOutside i hi
  have hSum : (∑ i, (massLower i : ℝ)) ≤ μ.real (⋃ i, cells i) := by
    calc
      _ ≤ ∑ i, μ.real (cells i) :=
        Finset.sum_le_sum (fun i _ => hMassLower i)
      _ = μ.real (⋃ i, cells i) :=
        (measureReal_iUnion_fintype hDisjoint hMeas).symm
  have hMonotone : μ.real (⋃ i, cells i) ≤ μ.real negativeᶜ :=
    measureReal_mono hUsubset
  have hProb : μ.real negative + μ.real negativeᶜ = 1 :=
    probReal_add_probReal_compl hNegative
  linarith only [hSum, hMonotone, hProb]

local notation "GR" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKR_group : IsTopologicalGroup GR :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKR_compact : CompactSpace GR :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKR_countable : SecondCountableTopology GR :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKR_measurable : MeasurableSpace GR :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKR_borel : BorelSpace GR :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKR_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "CfgR" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2
local notation "muR" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "uR" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer 14 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "mR" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin 14 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "negativeR" => {A : CfgR | uR A < -(mR)}

local instance p4Q2PZ37AKR_probability : IsProbabilityMeasure muR := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Existing AIT + AIB + AIW already provide an unconditional genuine
H14 lower Haar mass bound. This DOES NOT certify the AKQ upper bound. -/
theorem p4Q2PZ37AKR_originalH14_negativeHaarMass_ge_half :
    (1 / 2 : ℝ) ≤ Measure.real muR negativeR := by
  have hSeven : beta0 ≤ (7 : ℝ) := by
    have h := (p4Q2PZ37AIB_fixedCoupling_rationalInterval).2
    linarith only [h]
  have hHalf :=
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_of_le_seven
      14 beta0 p4Q2PZ37ADC_fixedCoupling_pos hSeven
  rw [← p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    14 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le] at hHalf
  exact hHalf

/-- The true H14 original negative-region measure is bounded by one
minus independently certified finite complementary Borel cell mass.
The pointwise rational transfer floors must enclose the ACTUAL u14;
they are never inferred from approximate values alone. -/
theorem p4Q2PZ37AKR_originalH14_negativeHaarMass_le_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgR)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (Disjoint on cells))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgR), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uR A)
    (hTransferAboveMargin : ∀ i, -(mR) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muR (cells i)) :
    Measure.real muR negativeR ≤ 1 - ∑ i, (massLower i : ℝ) := by
  have hNegative : MeasurableSet negativeR := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
      14 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le]
    exact p4Q2PZ37AIG_originalNegativeTransferRegion_measurable 14 beta0
  have hOutside : ∀ i, cells i ⊆ negativeRᶜ := by
    intro i A hCell hNegativeA
    have hLower := hTransferLower i A hCell
    have hMargin := hTransferAboveMargin i
    exact (not_lt_of_ge (hMargin.trans hLower)) hNegativeA
  have hMass :=
    real_probability_finite_complement_cells_budget_akr
      muR negativeR hNegative cells hMeas hDisjoint hOutside massLower hMassLower
  linarith only [hMass]

/-- A finite collection of certified positive-side cells with enough
original Haar mass proves AKQ's ORIGINAL mass-sensitive test. No
uncertified cell table is promoted to a physical claim. -/
theorem p4Q2PZ37AKR_originalH14_gaussianHaarTest_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgR)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (Disjoint on cells))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgR), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uR A)
    (hTransferAboveMargin : ∀ i, -(mR) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muR (cells i))
    (hTotal :
      (1 : ℝ) - 4 * Real.exp (-(beta0 ^ 2 * (81000 : ℝ) / 2)) ≤
        ∑ i, (massLower i : ℝ)) :
    Measure.real muR negativeR *
      Real.exp (beta0 ^ 2 * (81000 : ℝ) / 2) ≤ 4 := by
  let x : ℝ := beta0 ^ 2 * (81000 : ℝ) / 2
  have hCellMass :=
    p4Q2PZ37AKR_originalH14_negativeHaarMass_le_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower
  have hCut : (1 : ℝ) - 4 * Real.exp (-x) ≤ ∑ i, (massLower i : ℝ) :=
    hTotal
  have hBound : Measure.real muR negativeR ≤ 4 * Real.exp (-x) := by
    linarith only [hCellMass, hCut]
  calc
    _ ≤ (4 * Real.exp (-x)) * Real.exp x :=
      mul_le_mul_of_nonneg_right hBound (Real.exp_pos x).le
    _ = 4 * (Real.exp (-x) * Real.exp x) := by ring
    _ = 4 * Real.exp ((-x) + x) := by rw [Real.exp_add]
    _ = 4 := by simp

/-- Conditional original H14 finite-power AJA exclusion, with
computationally checkable rational Borel-cell input. -/
theorem p4Q2PZ37AKR_originalH14_no_AJA_witness_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgR)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (Disjoint on cells))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgR), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uR A)
    (hTransferAboveMargin : ∀ i, -(mR) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muR (cells i))
    (hTotal :
      (1 : ℝ) - 4 * Real.exp (-(beta0 ^ 2 * (81000 : ℝ) / 2)) ≤
        ∑ i, (massLower i : ℝ)) :
    ¬ ∃ k : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          14 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ k)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 14)‖ ^ 2 <
      (mR) ^ 2 * Measure.real muR negativeR := by
  have hMass :=
    p4Q2PZ37AKR_originalH14_gaussianHaarTest_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower hTotal
  exact p4Q2PZ37AKQ_originalH14_no_AJA_witness_of_genuineHaarMass hMass

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.real_probability_finite_complement_cells_budget_akr
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKR_originalH14_negativeHaarMass_ge_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKR_originalH14_negativeHaarMass_le_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKR_originalH14_gaussianHaarTest_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKR_originalH14_no_AJA_witness_of_rationalCells
