import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformSpatialHaarQuadratureV5_PZ37AGH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGI — signed finite interval certificates for original spatial Haar

AGH supplies arbitrary-accuracy quadrature existence. AGI separates an
actually computable rational table evaluator from the proof obligations
relating supplied table entries to the ORIGINAL continuous integrand,
original spatial Haar masses and AGG's original geometric slope.

For center intervals [a_i,b_i], true mass intervals [m_i,M_i] and a rational
geometric error gamma, set l_i=a_i-gamma and u_i=b_i+gamma. The exact
rational evaluator returns

  lower = sum_i min(l_i*m_i,l_i*M_i),
  upper = sum_i max(u_i*m_i,u_i*M_i).

Lower/upper genuine Haar step functions and integral monotonicity prove
lower <= t_H(B) <= upper. Signed products are NOT replaced by products
of lower endpoints: a negative l_i must use the upper mass endpoint.
No mass interval is silently treated as an exact numerical Haar mass.

Boolean positivity/negativity checks are sound only with the separate
physical certificate. Two certificates for the SAME original B, even
with different grids, admit a tighten-only intersection. The AFV interval
and AGA rational-ball interfaces retain the same actual transfer value.

The arithmetic regression tables below are SYNTHETIC checker tests, not
certified Wilson/Haar data. No actual physical sign, two-threshold shell,
volume-uniform coercivity, Hamiltonian or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Finite rational input data. This structure contains no real integral,
classical enclosure choice, or assumed physical sign. -/
structure p4Q2PZ37AGI_rationalTable (n : ℕ) where
  sampleLower : Fin n → ℚ
  sampleUpper : Fin n → ℚ
  massLower : Fin n → ℚ
  massUpper : Fin n → ℚ
  geometry : ℚ

namespace p4Q2PZ37AGI_rationalTable

variable {n : ℕ}

def cellLower (d : p4Q2PZ37AGI_rationalTable n) (i : Fin n) : ℚ :=
  d.sampleLower i - d.geometry

def cellUpper (d : p4Q2PZ37AGI_rationalTable n) (i : Fin n) : ℚ :=
  d.sampleUpper i + d.geometry

/-- Exact finite rational lower evaluator, including negative cells. -/
def lower (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, min (d.cellLower i * d.massLower i)
    (d.cellLower i * d.massUpper i)

/-- Exact finite rational upper evaluator, including negative cells. -/
def upper (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, max (d.cellUpper i * d.massLower i)
    (d.cellUpper i * d.massUpper i)

def acceptsPositive (d : p4Q2PZ37AGI_rationalTable n) : Bool :=
  decide (0 < d.lower)

def acceptsNegative (d : p4Q2PZ37AGI_rationalTable n) : Bool :=
  decide (d.upper < 0)

/-- Synthetic test only: no original physical realization is claimed. -/
def negativeTest : p4Q2PZ37AGI_rationalTable 1 where
  sampleLower := fun _ => -2
  sampleUpper := fun _ => -1
  massLower := fun _ => 1 / 4
  massUpper := fun _ => 1 / 2
  geometry := 0

/-- The negative lower endpoint must use the UPPER mass endpoint. -/
theorem negativeTest_checked :
    negativeTest.lower = -1 ∧ negativeTest.upper = -(1 / 4) ∧
      negativeTest.acceptsNegative = true ∧ negativeTest.acceptsPositive = false := by
  norm_num [negativeTest, lower, upper, cellLower, cellUpper,
    acceptsNegative, acceptsPositive]

/-- Synthetic positive arithmetic test, not a true transfer sample. -/
def positiveTest : p4Q2PZ37AGI_rationalTable 1 where
  sampleLower := fun _ => 1
  sampleUpper := fun _ => 2
  massLower := fun _ => 1 / 4
  massUpper := fun _ => 1 / 2
  geometry := 0

theorem positiveTest_checked :
    positiveTest.lower = 1 / 4 ∧ positiveTest.upper = 1 ∧
      positiveTest.acceptsPositive = true ∧ positiveTest.acceptsNegative = false := by
  norm_num [positiveTest, lower, upper, cellLower, cellUpper,
    acceptsNegative, acceptsPositive]

/-- Geometry can destroy a nominal center sign; the checker must abstain. -/
def uncertainTest : p4Q2PZ37AGI_rationalTable 1 where
  sampleLower := fun _ => 1 / 4
  sampleUpper := fun _ => 1 / 2
  massLower := fun _ => 1
  massUpper := fun _ => 1
  geometry := 1

theorem uncertainTest_checked :
    uncertainTest.lower = -(3 / 4) ∧ uncertainTest.upper = 3 / 2 ∧
      uncertainTest.acceptsPositive = false ∧ uncertainTest.acceptsNegative = false := by
  norm_num [uncertainTest, lower, upper, cellLower, cellUpper,
    acceptsNegative, acceptsPositive]

end p4Q2PZ37AGI_rationalTable

/-- Affine interval multiplication handles every coefficient sign.
Neither mass endpoint has to be artificially declared positive. -/
theorem p4Q2PZ37AGI_signedMul_bounds
    (a x lo hi : ℝ) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    min (a * lo) (a * hi) ≤ x * a ∧ x * a ≤ max (a * lo) (a * hi) := by
  by_cases ha : 0 ≤ a
  · constructor
    · calc
        min (a * lo) (a * hi) ≤ a * lo := min_le_left _ _
        _ ≤ a * x := mul_le_mul_of_nonneg_left hlo ha
        _ = x * a := mul_comm _ _
    · calc
        x * a = a * x := mul_comm _ _
        _ ≤ a * hi := mul_le_mul_of_nonneg_left hhi ha
        _ ≤ max (a * lo) (a * hi) := le_max_right _ _
  · have hna : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    constructor
    · calc
        min (a * lo) (a * hi) ≤ a * hi := min_le_right _ _
        _ ≤ a * x := mul_le_mul_of_nonpos_left hhi hna
        _ = x * a := mul_comm _ _
    · calc
        x * a = a * x := mul_comm _ _
        _ ≤ a * lo := mul_le_mul_of_nonpos_left hlo hna
        _ ≤ max (a * lo) (a * hi) := le_max_left _ _

noncomputable section
open scoped Topology Classical InnerProductSpace ENNReal

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGI_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGI_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGI_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGI_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable {H : ℕ}
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "slope" => p4Q2PZ37AGG_originalSpatialSlope H
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGI_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGI_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Evidence against actual original quantities, separate from computable
data. No truth claim about a table follows merely by running its checker. -/
structure p4Q2PZ37AGI_certifiedTable
    (H : ℕ)
    (boundary : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (data : p4Q2PZ37AGI_rationalTable grid.n) : Prop where
  hGeometry : p4Q2PZ37AGG_originalSpatialSlope H * grid.radius ≤ (data.geometry : ℝ)
  hCenterLower : ∀ i, (data.sampleLower i : ℝ) ≤
    p4Q2PZ37AGE_originalContinuousIntegrand H boundary (grid.center i)
  hCenterUpper : ∀ i,
    p4Q2PZ37AGE_originalContinuousIntegrand H boundary (grid.center i) ≤
      (data.sampleUpper i : ℝ)
  hMassLower : ∀ i, (data.massLower i : ℝ) ≤
    Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (grid.cell i)
  hMassUpper : ∀ i,
    Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (grid.cell i) ≤ (data.massUpper i : ℝ)

namespace p4Q2PZ37AGI_certifiedTable

variable {grid : p4Q2PZ37AGH_originalSpatialGrid H}
  {data : p4Q2PZ37AGI_rationalTable grid.n}

/-- Reuse the exact AGC Haar-step calculus. Midpoint weights and errors
are only an adapter; the signed proof integrates the TRUE cell masses. -/
def toHaarCells {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data) :
    p4Q2PZ37AGC_originalHaarCells H where
  n := grid.n
  cell := grid.cell
  hMeas := grid.hMeas
  hPartition := grid.hPartition
  weight := fun i => (data.massLower i + data.massUpper i) / 2
  weightError := fun i => ((data.massUpper i : ℝ) - (data.massLower i : ℝ)) / 2
  hWeightError_nonneg := fun i => div_nonneg
    (sub_nonneg.mpr ((c.hMassLower i).trans (c.hMassUpper i))) (by norm_num)
  hWeightAccuracy := by
    intro i
    have hlo := c.hMassLower i
    have hhi := c.hMassUpper i
    push_cast
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi]

/-- AGG promotes true CENTER intervals to true CELL intervals without
evaluating an arbitrary Haar-L2 representative at a chosen point. -/
theorem cell_bounds {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data)
    (i : Fin grid.n) (A : Cfg) (hA : A ∈ grid.cell i) :
    (data.cellLower i : ℝ) ≤ gCont boundary A ∧
      gCont boundary A ≤ (data.cellUpper i : ℝ) := by
  have hOsc : |gCont boundary A - gCont boundary (grid.center i)| ≤
      (data.geometry : ℝ) :=
    ((p4Q2PZ37AGG_originalContinuousIntegrand_allLinkChordalSlope
      H boundary A (grid.center i)).trans
      (mul_le_mul_of_nonneg_left (grid.hRadius i A hA)
        (p4Q2PZ37AGG_originalSpatialSlope_nonneg H))).trans c.hGeometry
  obtain ⟨hlo, hhi⟩ := abs_le.mp hOsc
  have hcl := c.hCenterLower i
  have hcu := c.hCenterUpper i
  constructor
  · dsimp [p4Q2PZ37AGI_rationalTable.cellLower]
    push_cast
    linarith only [hlo, hcl]
  · dsimp [p4Q2PZ37AGI_rationalTable.cellUpper]
    push_cast
    linarith only [hhi, hcu]

/-- Soundness of the finite signed rational evaluator for the UNCHANGED
original signed transfer. All integration is against original spatial Haar. -/
theorem transfer_bounds {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data) :
    (data.lower : ℝ) ≤ t boundary ∧ t boundary ≤ (data.upper : ℝ) := by
  let p := c.toHaarCells
  have hf : Integrable (gCont boundary) muH :=
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable boundary).congr
      (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H boundary)
  have hLoPoint : ∀ A : Cfg,
      p4Q2PZ37AGC_HaarStep p data.cellLower A ≤ gCont boundary A := by
    intro A
    obtain ⟨i, hi, _⟩ := grid.hPartition A
    rw [p4Q2PZ37AGC_HaarStep_eq_onCell p data.cellLower i A hi]
    exact (c.cell_bounds i A hi).1
  have hHiPoint : ∀ A : Cfg,
      gCont boundary A ≤ p4Q2PZ37AGC_HaarStep p data.cellUpper A := by
    intro A
    obtain ⟨i, hi, _⟩ := grid.hPartition A
    rw [p4Q2PZ37AGC_HaarStep_eq_onCell p data.cellUpper i A hi]
    exact (c.cell_bounds i A hi).2
  have hLoInt := integral_mono
    (p4Q2PZ37AGC_HaarStep_integrable p data.cellLower) hf hLoPoint
  have hHiInt := integral_mono hf
    (p4Q2PZ37AGC_HaarStep_integrable p data.cellUpper) hHiPoint
  rw [p4Q2PZ37AGC_HaarStep_integral p data.cellLower,
    p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H boundary] at hLoInt
  rw [p4Q2PZ37AGC_HaarStep_integral p data.cellUpper,
    p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H boundary] at hHiInt
  have hCastLo : (data.lower : ℝ) = ∑ i : Fin grid.n,
      min ((data.cellLower i : ℝ) * (data.massLower i : ℝ))
        ((data.cellLower i : ℝ) * (data.massUpper i : ℝ)) := by
    simp [p4Q2PZ37AGI_rationalTable.lower]
  have hCastHi : (data.upper : ℝ) = ∑ i : Fin grid.n,
      max ((data.cellUpper i : ℝ) * (data.massLower i : ℝ))
        ((data.cellUpper i : ℝ) * (data.massUpper i : ℝ)) := by
    simp [p4Q2PZ37AGI_rationalTable.upper]
  have hLoSum : (data.lower : ℝ) ≤ ∑ i : Fin grid.n,
      Measure.real muH (grid.cell i) * (data.cellLower i : ℝ) := by
    rw [hCastLo]
    apply Finset.sum_le_sum
    intro i _hi
    exact (p4Q2PZ37AGI_signedMul_bounds (data.cellLower i : ℝ)
      (Measure.real muH (grid.cell i)) (data.massLower i : ℝ) (data.massUpper i : ℝ)
      (c.hMassLower i) (c.hMassUpper i)).1
  have hHiSum : (∑ i : Fin grid.n,
      Measure.real muH (grid.cell i) * (data.cellUpper i : ℝ)) ≤ (data.upper : ℝ) := by
    rw [hCastHi]
    apply Finset.sum_le_sum
    intro i _hi
    exact (p4Q2PZ37AGI_signedMul_bounds (data.cellUpper i : ℝ)
      (Measure.real muH (grid.cell i)) (data.massLower i : ℝ) (data.massUpper i : ℝ)
      (c.hMassLower i) (c.hMassUpper i)).2
  exact ⟨hLoSum.trans hLoInt, hHiInt.trans hHiSum⟩

/-- Existing AFV semantics, with literal computed rational endpoints. -/
def toVerifiedInterval {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data) :
    p4Q2PZ37AFV_verifiedInterval (t boundary) where
  lower := data.lower
  upper := data.upper
  hLower := c.transfer_bounds.1
  hUpper := c.transfer_bounds.2

/-- Existing AGA factor interfaces receive the SAME original transfer. -/
def toRationalBall {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data) :
    p4Q2PZ37AGA_rationalBall (t boundary) :=
  p4Q2PZ37AGA_fromVerifiedInterval c.toVerifiedInterval

/-- A purely rational positive check becomes physical only with c. -/
theorem positive_of_accepts {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data)
    (h : data.acceptsPositive = true) : 0 < t boundary := by
  have hq : 0 < data.lower := of_decide_eq_true h
  have hr : (0 : ℝ) < (data.lower : ℝ) := by exact_mod_cast hq
  exact hr.trans_le c.transfer_bounds.1

/-- Corresponding negative check; no sign is invented by approximation. -/
theorem negative_of_accepts {boundary : Cfg}
    (c : p4Q2PZ37AGI_certifiedTable H boundary grid data)
    (h : data.acceptsNegative = true) : t boundary < 0 := by
  have hq : data.upper < 0 := of_decide_eq_true h
  have hr : (data.upper : ℝ) < 0 := by exact_mod_cast hq
  exact c.transfer_bounds.2.trans_lt hr

/-- Independently supplied grids can be combined by intersection because
both certificates retain the SAME original H, B, source and Haar law. -/
def intersectInterval {boundary : Cfg}
    {grid₂ : p4Q2PZ37AGH_originalSpatialGrid H}
    {data₂ : p4Q2PZ37AGI_rationalTable grid₂.n}
    (c₁ : p4Q2PZ37AGI_certifiedTable H boundary grid data)
    (c₂ : p4Q2PZ37AGI_certifiedTable H boundary grid₂ data₂) :
    p4Q2PZ37AFV_verifiedInterval (t boundary) where
  lower := max data.lower data₂.lower
  upper := min data.upper data₂.upper
  hLower := by
    have h := max_le c₁.transfer_bounds.1 c₂.transfer_bounds.1
    simpa using h
  hUpper := by
    have h := le_min c₁.transfer_bounds.2 c₂.transfer_bounds.2
    simpa using h

/-- Correct tables on different grids cannot certify contradictory signs. -/
theorem no_opposite_certified_signs {boundary : Cfg}
    {grid₂ : p4Q2PZ37AGH_originalSpatialGrid H}
    {data₂ : p4Q2PZ37AGI_rationalTable grid₂.n}
    (c₁ : p4Q2PZ37AGI_certifiedTable H boundary grid data)
    (c₂ : p4Q2PZ37AGI_certifiedTable H boundary grid₂ data₂)
    (hp : data.acceptsPositive = true) (hn : data₂.acceptsNegative = true) : False := by
  have hpos := c₁.positive_of_accepts hp
  have hneg := c₂.negative_of_accepts hn
  exact (not_lt_of_ge hpos.le) hneg

end p4Q2PZ37AGI_certifiedTable
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_rationalTable.negativeTest_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_rationalTable.positiveTest_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_rationalTable.uncertainTest_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_signedMul_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.toHaarCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.cell_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.transfer_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.toVerifiedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.toRationalBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.positive_of_accepts
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.negative_of_accepts
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.intersectInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGI_certifiedTable.no_opposite_certified_signs
