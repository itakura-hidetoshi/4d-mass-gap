import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH22GenuineHaarThresholdV5_PZ37AKX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH14ComplementBorelCellCertificateV5_PZ37AKR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKY — genuine H22 complement Haar-cell descent

Keep exactly the original SU(2) spatial product Haar, Wilson transfer,
normalized physical operator and ZW source, original AIG margin and strict
negative event, the AKU full-top projection, and beta0=log(3/2)/64.
The AKX H22 criterion is a genuine sufficient upper Haar-mass condition,
not an observed H22 mass value.

This leaf transfers AKR's finite complementary Borel-cell bookkeeping to
the original H22 configuration, where the exact AKW/AKX coefficient is
44/351 and the exact original plaquette count is 292008. Any cells must
have independently checked universal pointwise transfer lower floors
and genuine original Haar lower masses. Their combined certified lower
mass must exceed the exact complementary threshold
  1 - 4*exp(-(44/351)*beta0^2*292008).

This constructs an auditable conditional descent from actual cells to
the original H22 AJA no-witness and full-top comparison. It does NOT
construct any actual cells, prove a numerical r22 upper bound, show an
unconditional H22 no-witness, or establish a Hamiltonian/continuum gap.
The already certified AIT half-Haar LOWER bound is separately recorded;
it does NOT yield the upper bound demanded by AKX.
No original physical definitions, existing theorem statements,
dependency pins, root, assumptions, or workflows are modified.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GY" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKY_group : IsTopologicalGroup GY :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKY_compact : CompactSpace GY :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKY_countable : SecondCountableTopology GY :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKY_measurable : MeasurableSpace GY :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKY_borel : BorelSpace GY :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKY_links :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink 22) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "CfgY" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 22 2
local notation "muY" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 22 2
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "uY" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer 22 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "mY" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin 22 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "negativeY" => (fun A : CfgY => uY A < -(mY))
local notation "rY" => Measure.real muY negativeY
local notation "qY" => 44 * beta0 ^ 2 * (292008 : ℝ) / 351

local instance p4Q2PZ37AKY_probability : IsProbabilityMeasure muY := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

private theorem originalH22_negativeY_measurable : MeasurableSet negativeY := by
  have hOriginal :=
    p4Q2PZ37AIG_originalNegativeTransferRegion_measurable 22 beta0
  rw [← p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    22 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le] at hOriginal
  exact hOriginal

/-- Actual H22 original Haar-negative region has the independently
certified HALF-MASS LOWER bound, NOT an AKX upper bound. -/
theorem p4Q2PZ37AKY_originalH22_negativeHaarMass_ge_half :
    (1 / 2 : ℝ) ≤ rY := by
  have hSeven : beta0 ≤ (7 : ℝ) := by
    have h := (p4Q2PZ37AIB_fixedCoupling_rationalInterval).2
    linarith only [h]
  have hHalf :=
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_of_le_seven
      22 beta0 p4Q2PZ37ADC_fixedCoupling_pos hSeven
  rw [← p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
    22 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le] at hHalf
  exact hHalf

/-- The true H22 positive-side complement has Haar mass at most one
half, a compatibility constraint on any proposed complementary cells. -/
theorem p4Q2PZ37AKY_originalH22_complementHaarMass_le_half :
    Measure.real muY negativeYᶜ ≤ (1 / 2 : ℝ) := by
  have hProb : rY + Measure.real muY negativeYᶜ = 1 :=
    probReal_add_probReal_compl originalH22_negativeY_measurable
  have hHalf := p4Q2PZ37AKY_originalH22_negativeHaarMass_ge_half
  linarith only [hProb, hHalf]

/-- A finite set of actual H22 Borel cells with certified rational
pointwise transfer floors and Haar lower masses yields a genuine
negative-region upper bound. All cell obligations are explicit. -/
theorem p4Q2PZ37AKY_originalH22_negativeHaarMass_le_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgY), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uY A)
    (hTransferAboveMargin : ∀ i, -(mY) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i)) :
    rY ≤ 1 - ∑ i, (massLower i : ℝ) := by
  have hOutside : ∀ i, cells i ⊆ negativeYᶜ := by
    intro i A hCell hNegativeA
    have hLower := hTransferLower i A hCell
    have hMargin := hTransferAboveMargin i
    exact (not_lt_of_ge (hMargin.trans hLower)) hNegativeA
  have hMass :=
    real_probability_finite_complement_cells_budget_akr
      muY negativeY originalH22_negativeY_measurable cells
      hMeas hDisjoint hOutside massLower hMassLower
  linarith only [hMass]

/-- All admissible lower cell masses together cannot exceed 1/2:
this bound is an unconditional H22 compatibility check and is
different in direction from the required AKX threshold. -/
theorem p4Q2PZ37AKY_originalH22_certifiedCellTotal_le_half
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hOutside : ∀ i, cells i ⊆ negativeYᶜ)
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i)) :
    (∑ i, (massLower i : ℝ)) ≤ (1 / 2 : ℝ) := by
  have hMass :=
    real_probability_finite_complement_cells_budget_akr
      muY negativeY originalH22_negativeY_measurable cells
      hMeas hDisjoint hOutside massLower hMassLower
  have hHalf := p4Q2PZ37AKY_originalH22_negativeHaarMass_ge_half
  linarith only [hMass, hHalf]

/-- An actual H22 complementary-cell lower mass meeting the *exact*
AKX cutoff yields the missing genuine original Haar-mass hypothesis.
This remains conditional until concrete cells are constructed. -/
theorem p4Q2PZ37AKY_originalH22_massThreshold_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgY), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uY A)
    (hTransferAboveMargin : ∀ i, -(mY) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i))
    (hTotal : (1 : ℝ) - 4 * Real.exp (-qY) ≤
      ∑ i, (massLower i : ℝ)) :
    rY ≤ 4 * Real.exp (-qY) := by
  have hCells :=
    p4Q2PZ37AKY_originalH22_negativeHaarMass_le_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower
  linarith only [hCells, hTotal]

/-- Original H22 finite strict AJA witness excluded *only if* the
actual complementary Borel-cell certificate is separately supplied. -/
theorem p4Q2PZ37AKY_originalH22_no_AJA_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgY), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uY A)
    (hTransferAboveMargin : ∀ i, -(mY) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i))
    (hTotal : (1 : ℝ) - 4 * Real.exp (-qY) ≤
      ∑ i, (massLower i : ℝ)) :
    ¬ ∃ k : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          22 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ k)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 22)‖ ^ 2 <
      (mY) ^ 2 * rY := by
  exact p4Q2PZ37AKX_originalH22_no_AJA_of_genuineHaarMass
    (p4Q2PZ37AKY_originalH22_massThreshold_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower hTotal)

/-- Same original-cell hypothesis gives the true full-top budget bound. -/
theorem p4Q2PZ37AKY_originalH22_budget_le_fullTop_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgY), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uY A)
    (hTransferAboveMargin : ∀ i, -(mY) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i))
    (hTotal : (1 : ℝ) - 4 * Real.exp (-qY) ≤
      ∑ i, (massLower i : ℝ)) :
    (mY) ^ 2 * rY ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent 22 beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKX_originalH22_budget_le_top_of_genuineHaarMass
    (p4Q2PZ37AKY_originalH22_massThreshold_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower hTotal)

/-- Original H22 residual is nonpositive under the identical cells;
a strict sign or any unconditional H22 claim is not proved. -/
theorem p4Q2PZ37AKY_originalH22_delta_nonpos_of_rationalCells
    {n : ℕ} (cells : Fin n → Set CfgY)
    (hMeas : ∀ i, MeasurableSet (cells i))
    (hDisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (transferFloor : Fin n → ℚ)
    (hTransferLower : ∀ i (A : CfgY), A ∈ cells i →
      (transferFloor i : ℝ) ≤ uY A)
    (hTransferAboveMargin : ∀ i, -(mY) ≤ (transferFloor i : ℝ))
    (massLower : Fin n → ℚ)
    (hMassLower : ∀ i, (massLower i : ℝ) ≤ Measure.real muY (cells i))
    (hTotal : (1 : ℝ) - 4 * Real.exp (-qY) ≤
      ∑ i, (massLower i : ℝ)) :
    (mY) ^ 2 * rY -
      ‖p4Q2PZ37AJD_originalSourceTopComponent 22 beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKY_originalH22_budget_le_fullTop_of_rationalCells
      cells hMeas hDisjoint transferFloor hTransferLower
      hTransferAboveMargin massLower hMassLower hTotal)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_negativeHaarMass_ge_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_complementHaarMass_le_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_negativeHaarMass_le_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_certifiedCellTotal_le_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_massThreshold_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_no_AJA_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_budget_le_fullTop_of_rationalCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKY_originalH22_delta_nonpos_of_rationalCells
