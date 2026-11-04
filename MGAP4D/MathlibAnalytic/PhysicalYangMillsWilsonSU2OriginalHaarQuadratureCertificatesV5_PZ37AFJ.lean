import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCoefficientIntervalBudgetsV5_PZ37AFI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFJ — genuine Haar finite-cell quadrature certificates

AFI reduces true Wilson/Perron Haar-shell interval certification to proved
approximation errors for four original SU(2) Haar coefficients and for the
original receiver variance at the finite AFG boundary net.

AFJ constructs the latter from three families of SAME-RECEIVER single-link
Haar integrals. For each genuine finite boundary configuration z, certify
a finite measurable partition of SU(2) with rational approximations to
the TRUE Haar cell masses, together with certified cellwise enclosures for
the actual receiver F_z, its square F_z^2, and the four actual integrands
F_z * phi_j. Every hypothesis refers to original Wilson/Perron functions.

For any continuous f, a finite rational table q_i with a rigorously
certified cellwise uniform error eps and rational mass weights p_i with
errors dw_i yields

 |integral_mu f - sum_i (q_i * p_i)|
   <= eps + sum_i |q_i| * dw_i.

The proof integrates the finite measurable indicator decomposition under
the UNCHANGED normalized SU(2) Haar probability; no discrete substitute
measure is installed. The exact original centered receiver variance is
  V_z = integral_mu F_z^2 - (integral_mu F_z)^2.
Consequently two independently certified finite tables for the mean and
second moment produce a rigorously certified rational variance center,
with error deltaV = deltaSecond + deltaMean*(2*|meanHat|+deltaMean).
Four similarly certified integrals produce AFI's actual coefficient error
proofs, and hence AFH original Haar-shell and packing certificates.

The existence of rational cell tables with verified positive error budgets,
their concrete numerical evaluation, nonempty threshold crossings, any
H-uniform coercivity or the continuum Yang--Mills mass gap is NOT claimed.
All certified cells and weights are premises that must be independently
established for an actual numeric application.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFJ_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFJ_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFJ_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFJ_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFJ_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H

local instance p4Q2PZ37AFJ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFJ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Real measurable SU(2) partition with independently certified
rational approximations of the TRUE original normalized Haar cell masses.
The table is finite, but its conditions are mathematical proof evidence,
not unvalidated numerical assertions. -/
structure p4Q2PZ37AFJ_originalHaarCells where
  n : ℕ
  cell : Fin n → Set G
  hMeas : ∀ i, MeasurableSet (cell i)
  hPartition : ∀ g : G, ∃ i : Fin n,
    g ∈ cell i ∧ ∀ j : Fin n, g ∈ cell j → j = i
  weight : Fin n → ℚ
  weightError : Fin n → ℝ
  hWeightError_nonneg : ∀ i, 0 ≤ weightError i
  hWeightAccuracy : ∀ i,
    |Measure.real mu (cell i) - (weight i : ℝ)| ≤ weightError i

/-- A truly finite simple function, integrated against original Haar. -/
def p4Q2PZ37AFJ_HaarStep
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) (g : G) : ℝ :=
  ∑ i : Fin p.n, (p.cell i).indicator (fun _ : G => (q i : ℝ)) g

/-- Rational finite weighted estimate, with no floating-point casts. -/
def p4Q2PZ37AFJ_HaarCenter
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) : ℚ :=
  ∑ i : Fin p.n, q i * p.weight i

/-- Error from certified rational mass approximations only. -/
def p4Q2PZ37AFJ_HaarWeightError
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) : ℝ :=
  ∑ i : Fin p.n, |(q i : ℝ)| * p.weightError i

/-- Explicit total error budget including cell oscillation. -/
def p4Q2PZ37AFJ_HaarTotalError
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) (eps : ℝ) : ℝ :=
  eps + p4Q2PZ37AFJ_HaarWeightError p q

/-- Exactly one cell contributes at any point of the genuine Haar
partition. This prevents double counting of overlapping cells. -/
theorem p4Q2PZ37AFJ_HaarStep_eq_onCell
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) (i : Fin p.n) (g : G)
    (hi : g ∈ p.cell i) :
    p4Q2PZ37AFJ_HaarStep p q g = (q i : ℝ) := by
  classical
  have hUnique := p.hPartition g
  obtain ⟨k, hk, hOnly⟩ := hUnique
  have hI : i = k := hOnly i hi
  have hNot (j : Fin p.n) (hj : j ≠ i) : g ∉ p.cell j := by
    intro h
    have heq : j = i := (hOnly j h).trans hI.symm
    exact hj heq
  unfold p4Q2PZ37AFJ_HaarStep
  calc
    (∑ j : Fin p.n, (p.cell j).indicator (fun _ : G => (q j : ℝ)) g) =
        ∑ j : Fin p.n, if j = i then (q i : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [Set.indicator_of_mem hi]
      · simp [Set.indicator, hj, hNot j hj]
    _ = (q i : ℝ) := by simp

/-- Cellwise physical integrand bounds imply a bound everywhere
against the actual finite Haar step function. -/
theorem p4Q2PZ37AFJ_HaarStep_pointwise_bound
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) (f : G → ℝ) (eps : ℝ)
    (hLocal : ∀ i (g : G), g ∈ p.cell i →
      |f g - (q i : ℝ)| ≤ eps) :
    ∀ g : G, |f g - p4Q2PZ37AFJ_HaarStep p q g| ≤ eps := by
  intro g
  obtain ⟨i, hi, _⟩ := p.hPartition g
  rw [p4Q2PZ37AFJ_HaarStep_eq_onCell p q i g hi]
  exact hLocal i g hi

/-- Each genuine measurable Haar step is integrable on the
unchanged normalized Haar probability. -/
theorem p4Q2PZ37AFJ_HaarStep_integrable
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) :
    Integrable (p4Q2PZ37AFJ_HaarStep p q) mu := by
  unfold p4Q2PZ37AFJ_HaarStep
  apply integrable_finset_sum
  intro i _
  exact (integrable_const (q i : ℝ)).indicator (p.hMeas i)

/-- Exact finite indicator integration uses ORIGINAL normalized Haar,
not the rational approximate weights. -/
theorem p4Q2PZ37AFJ_HaarStep_integral
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) :
    (∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu) =
      ∑ i : Fin p.n, Measure.real mu (p.cell i) * (q i : ℝ) := by
  unfold p4Q2PZ37AFJ_HaarStep
  rw [integral_finset_sum Finset.univ
    (fun i _ => (integrable_const (q i : ℝ)).indicator (p.hMeas i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const (q i : ℝ) (p.hMeas i), smul_eq_mul]

/-- Finite rational-weight error bound for genuine Haar step integrals. -/
theorem p4Q2PZ37AFJ_HaarStep_weightError
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) :
    |(∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu) -
      (p4Q2PZ37AFJ_HaarCenter p q : ℝ)| ≤
        p4Q2PZ37AFJ_HaarWeightError p q := by
  rw [p4Q2PZ37AFJ_HaarStep_integral]
  have hCast : (p4Q2PZ37AFJ_HaarCenter p q : ℝ) =
      ∑ i : Fin p.n, (q i : ℝ) * (p.weight i : ℝ) := by
    simp [p4Q2PZ37AFJ_HaarCenter]
  rw [hCast]
  have hTerm (i : Fin p.n) :
      |Measure.real mu (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ)| ≤
            |(q i : ℝ)| * p.weightError i := by
    have h := p.hWeightAccuracy i
    have hEq : Measure.real mu (p.cell i) * (q i : ℝ) -
        (q i : ℝ) * (p.weight i : ℝ) =
          (q i : ℝ) * (Measure.real mu (p.cell i) - (p.weight i : ℝ)) := by
      ring
    rw [hEq, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  calc
    |(∑ i : Fin p.n, Measure.real mu (p.cell i) * (q i : ℝ)) -
      (∑ i : Fin p.n, (q i : ℝ) * (p.weight i : ℝ))| =
      |∑ i : Fin p.n,
        (Measure.real mu (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin p.n,
        |Measure.real mu (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ p4Q2PZ37AFJ_HaarWeightError p q := by
      unfold p4Q2PZ37AFJ_HaarWeightError
      exact Finset.sum_le_sum (fun i _ => hTerm i)

/-- A single total error bound from FINITE, cellwise, rational data
and certified true Haar cell masses. Genuine integrands stay unchanged. -/
theorem p4Q2PZ37AFJ_integral_error_of_cells
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (f : G → ℝ) (q : Fin p.n → ℚ) (eps : ℝ)
    (hf : Continuous f)
    (hLocal : ∀ i (g : G), g ∈ p.cell i →
      |f g - (q i : ℝ)| ≤ eps) :
    |(∫ g : G, f g ∂mu) -
      (p4Q2PZ37AFJ_HaarCenter p q : ℝ)| ≤
        p4Q2PZ37AFJ_HaarTotalError p q eps := by
  have hF : Integrable f mu :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hStep := p4Q2PZ37AFJ_HaarStep_integrable p q
  have hPoint : |(∫ g : G, f g ∂mu) -
      (∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu)| ≤ eps := by
    have hNorm := norm_integral_le_of_norm_le_const
      (μ := mu) (f := fun g : G => f g - p4Q2PZ37AFJ_HaarStep p q g)
      (C := eps) (Filter.Eventually.of_forall (fun g : G => by
        simpa only [Real.norm_eq_abs] using
          p4Q2PZ37AFJ_HaarStep_pointwise_bound p q f eps hLocal g))
    rw [← integral_sub hF hStep]
    simpa [Real.norm_eq_abs] using hNorm
  have hWeight := p4Q2PZ37AFJ_HaarStep_weightError p q
  calc
    |(∫ g : G, f g ∂mu) -
        (p4Q2PZ37AFJ_HaarCenter p q : ℝ)| =
      |((∫ g : G, f g ∂mu) -
          (∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu)) +
        ((∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu) -
          (p4Q2PZ37AFJ_HaarCenter p q : ℝ))| := by
        congr 1
        ring
    _ ≤ |(∫ g : G, f g ∂mu) -
          (∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu)| +
        |(∫ g : G, p4Q2PZ37AFJ_HaarStep p q g ∂mu) -
          (p4Q2PZ37AFJ_HaarCenter p q : ℝ)| :=
      abs_add_le _ _
    _ ≤ p4Q2PZ37AFJ_HaarTotalError p q eps := by
      unfold p4Q2PZ37AFJ_HaarTotalError
      exact add_le_add hPoint hWeight

/-- Finite error budgets are nonnegative whenever the cellwise
oscillation budget is nonnegative. -/
theorem p4Q2PZ37AFJ_HaarTotalError_nonneg
    (p : p4Q2PZ37AFJ_originalHaarCells)
    (q : Fin p.n → ℚ) (eps : ℝ) (hEps : 0 ≤ eps) :
    0 ≤ p4Q2PZ37AFJ_HaarTotalError p q eps := by
  unfold p4Q2PZ37AFJ_HaarTotalError p4Q2PZ37AFJ_HaarWeightError
  apply add_nonneg hEps
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (abs_nonneg _) (p.hWeightError_nonneg i)

/-- Quantitative square error for a mean reconstructed from the SAME
genuine Haar integral and a certified rational finite-cell center. -/
private theorem p4Q2PZ37AFJ_square_error
    (x y delta : ℝ) (hDelta : 0 ≤ delta)
    (h : |x - y| ≤ delta) :
    |x^2 - y^2| ≤ delta * (2 * |y| + delta) := by
  have hPlus : |x + y| ≤ 2 * |y| + delta := by
    calc
      |x + y| = |(x-y) + (y+y)| := by congr 1; ring
      _ ≤ |x-y| + |y+y| := abs_add_le _ _
      _ ≤ delta + (|y|+|y|) :=
        add_le_add h (abs_add_le _ _)
      _ = 2 * |y| + delta := by ring
  calc
    |x^2 - y^2| = |x-y| * |x+y| := by
      rw [show x^2-y^2=(x-y)*(x+y) by ring, abs_mul]
    _ ≤ delta * |x+y| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ ≤ delta * (2*|y|+delta) :=
      mul_le_mul_of_nonneg_left hPlus hDelta

/-- One shared, finite original Haar partition carries certificates
for all actual sampled receiver means, second moments and four
fundamental Haar coefficient integrands. -/
structure p4Q2PZ37AFJ_originalReceiverQuadrature
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  partition : p4Q2PZ37AFJ_originalHaarCells
  hThetaLo : 0 ≤ lo
  coefficientSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
        Fin 4 → Fin partition.n → ℚ
  coefficientOsc :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → Fin 4 → ℝ
  hCoefficientOsc_nonneg : ∀ a ∈ c.s, ∀ j, 0 ≤ coefficientOsc a j
  hCoefficientLocal : ∀ a ∈ c.s, ∀ j i (g : G),
    g ∈ partition.cell i →
      |p4Q2PZ37ABZ_originalReceiverSection H
        p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g *
        p4Q2PZ37ACK_fourModeCharacter j g -
        (coefficientSample a j i : ℝ)| ≤ coefficientOsc a j
  meanSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
        Fin partition.n → ℚ
  meanOsc :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hMeanOsc_nonneg : ∀ a ∈ c.s, 0 ≤ meanOsc a
  hMeanLocal : ∀ a ∈ c.s, ∀ i (g : G), g ∈ partition.cell i →
    |p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g -
      (meanSample a i : ℝ)| ≤ meanOsc a
  secondSample :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
        Fin partition.n → ℚ
  secondOsc :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hSecondOsc_nonneg : ∀ a ∈ c.s, 0 ≤ secondOsc a
  hSecondLocal : ∀ a ∈ c.s, ∀ i (g : G), g ∈ partition.cell i →
    |(p4Q2PZ37ABZ_originalReceiverSection H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e a g)^2 -
      (secondSample a i : ℝ)| ≤ secondOsc a

/-- The four finite rational quadrature results are exactly rational. -/
def p4Q2PZ37AFJ_originalCoefficientCenter
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (j : Fin 4) : ℚ :=
  p4Q2PZ37AFJ_HaarCenter d.partition (d.coefficientSample a j)

/-- Exact, nonnegative error budget for each genuine ACK coefficient. -/
def p4Q2PZ37AFJ_originalCoefficientError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (j : Fin 4) : ℝ :=
  p4Q2PZ37AFJ_HaarTotalError d.partition
    (d.coefficientSample a j) (d.coefficientOsc a j)

/-- Rational original receiver mean, reconstructed from finite cells. -/
def p4Q2PZ37AFJ_originalMeanCenter
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℚ :=
  p4Q2PZ37AFJ_HaarCenter d.partition (d.meanSample a)

/-- Total genuine mean integral error for the original receiver. -/
def p4Q2PZ37AFJ_originalMeanError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℝ :=
  p4Q2PZ37AFJ_HaarTotalError d.partition (d.meanSample a) (d.meanOsc a)

/-- Rational second moment for the original receiver, same Haar law. -/
def p4Q2PZ37AFJ_originalSecondCenter
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℚ :=
  p4Q2PZ37AFJ_HaarCenter d.partition (d.secondSample a)

/-- Total genuine second moment error. -/
def p4Q2PZ37AFJ_originalSecondError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℝ :=
  p4Q2PZ37AFJ_HaarTotalError d.partition (d.secondSample a) (d.secondOsc a)

/-- The genuine variance's rational candidate is SECOND moment less
the square of the rational MEAN candidate, not an independent proxy. -/
def p4Q2PZ37AFJ_originalVarianceCenter
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℚ :=
  p4Q2PZ37AFJ_originalSecondCenter H e c d a -
    (p4Q2PZ37AFJ_originalMeanCenter H e c d a)^2

/-- Full quantitative variance error, including mean-square propagation. -/
def p4Q2PZ37AFJ_originalVarianceError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) : ℝ :=
  p4Q2PZ37AFJ_originalSecondError H e c d a +
    p4Q2PZ37AFJ_originalMeanError H e c d a *
      (2 * |(p4Q2PZ37AFJ_originalMeanCenter H e c d a : ℝ)| +
        p4Q2PZ37AFJ_originalMeanError H e c d a)

local notation "cHat" => p4Q2PZ37AFJ_originalCoefficientCenter H
local notation "cErr" => p4Q2PZ37AFJ_originalCoefficientError H
local notation "uHat" => p4Q2PZ37AFJ_originalMeanCenter H
local notation "uErr" => p4Q2PZ37AFJ_originalMeanError H
local notation "sHat" => p4Q2PZ37AFJ_originalSecondCenter H
local notation "sErr" => p4Q2PZ37AFJ_originalSecondError H
local notation "vHat" => p4Q2PZ37AFJ_originalVarianceCenter H
local notation "vErr" => p4Q2PZ37AFJ_originalVarianceError H

/-- Genuine original four-mode coefficients have certified finite-cell
rational enclosures, with no replacement Haar probability. -/
theorem p4Q2PZ37AFJ_originalCoefficient_accuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) :
    |m b0 hb0 e a j - (cHat e c d a j : ℝ)| ≤ cErr e c d a j := by
  have hF := p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a
  have hPhi := p4Q2PZ37ACK_fourModeCharacter_continuous j
  change |(∫ g : G, F b0 hb0 f0 e a g * phi j g ∂mu) -
    (p4Q2PZ37AFJ_HaarCenter d.partition (d.coefficientSample a j) : ℝ)| ≤
      p4Q2PZ37AFJ_HaarTotalError d.partition
        (d.coefficientSample a j) (d.coefficientOsc a j)
  exact p4Q2PZ37AFJ_integral_error_of_cells d.partition
    (fun g : G => F b0 hb0 f0 e a g * phi j g)
    (d.coefficientSample a j) (d.coefficientOsc a j)
    (hF.mul hPhi) (d.hCoefficientLocal a ha j)

/-- The original receiver mean is enclosed by a finite rational
quadrature center with an explicit certified error. -/
theorem p4Q2PZ37AFJ_originalMean_accuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    |(∫ g : G, F b0 hb0 f0 e a g ∂mu) - (uHat e c d a : ℝ)| ≤
      uErr e c d a :=
  p4Q2PZ37AFJ_integral_error_of_cells d.partition
    (F b0 hb0 f0 e a) (d.meanSample a) (d.meanOsc a)
    (p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a)
    (d.hMeanLocal a ha)

/-- Original receiver second moment similarly admits an independent
finite rational quadrature error certificate on SAME Haar cells. -/
theorem p4Q2PZ37AFJ_originalSecond_accuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    |(∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
      (sHat e c d a : ℝ)| ≤ sErr e c d a :=
  p4Q2PZ37AFJ_integral_error_of_cells d.partition
    (fun g : G => (F b0 hb0 f0 e a g)^2)
    (d.secondSample a) (d.secondOsc a)
    ((p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a).pow 2)
    (d.hSecondLocal a ha)

/-- AFJ variance error is always nonnegative when the finite
cellwise oscillations were proved nonnegative. -/
theorem p4Q2PZ37AFJ_originalVarianceError_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤ vErr e c d a := by
  unfold p4Q2PZ37AFJ_originalVarianceError
  have hu : 0 ≤ uErr e c d a :=
    p4Q2PZ37AFJ_HaarTotalError_nonneg d.partition (d.meanSample a)
      (d.meanOsc a) (d.hMeanOsc_nonneg a ha)
  have hs : 0 ≤ sErr e c d a :=
    p4Q2PZ37AFJ_HaarTotalError_nonneg d.partition (d.secondSample a)
      (d.secondOsc a) (d.hSecondOsc_nonneg a ha)
  exact add_nonneg hs (mul_nonneg hu
    (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hu))

/-- True original Wilson/Perron variance equals second Haar moment
minus the squared first Haar moment. There is no substituted receiver. -/
theorem p4Q2PZ37AFJ_originalVariance_moment_identity
    (e : Link) (a : Pair) :
    V b0 hb0 e a =
      (∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
        (∫ g : G, F b0 hb0 f0 e a g ∂mu)^2 := by
  unfold p4Q2PZ37ACL_originalCenteredReceiverVariance
    CompactEnergyMismatchMoment.variance
    CompactEnergyMismatchMoment.covariance
  simp only [pow_two]

/-- Mean- and second-moment errors propagate to true original
variance, including the nonlinear squared mean correction. -/
theorem p4Q2PZ37AFJ_originalVariance_accuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    |V b0 hb0 e a - (vHat e c d a : ℝ)| ≤ vErr e c d a := by
  have hMean := p4Q2PZ37AFJ_originalMean_accuracy H e c d a ha
  have hSecond := p4Q2PZ37AFJ_originalSecond_accuracy H e c d a ha
  have hMeanErrorNonneg : 0 ≤ uErr e c d a :=
    p4Q2PZ37AFJ_HaarTotalError_nonneg d.partition
      (d.meanSample a) (d.meanOsc a) (d.hMeanOsc_nonneg a ha)
  have hSquare := p4Q2PZ37AFJ_square_error
    (∫ g : G, F b0 hb0 f0 e a g ∂mu)
    (uHat e c d a : ℝ) (uErr e c d a) hMeanErrorNonneg hMean
  rw [p4Q2PZ37AFJ_originalVariance_moment_identity H e a]
  dsimp only [p4Q2PZ37AFJ_originalVarianceCenter,
    p4Q2PZ37AFJ_originalVarianceError]
  push_cast
  have hRearrange :
      ((∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
        (∫ g : G, F b0 hb0 f0 e a g ∂mu)^2) -
        ((sHat e c d a : ℝ) - (uHat e c d a : ℝ)^2) =
      ((∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
        (sHat e c d a : ℝ)) -
        ((∫ g : G, F b0 hb0 f0 e a g ∂mu)^2 -
          (uHat e c d a : ℝ)^2) := by ring
  rw [hRearrange]
  have hTriangle :
      |((∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
            (sHat e c d a : ℝ)) -
        ((∫ g : G, F b0 hb0 f0 e a g ∂mu)^2 -
          (uHat e c d a : ℝ)^2)| ≤
        |(∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
          (sHat e c d a : ℝ)| +
        |(∫ g : G, F b0 hb0 f0 e a g ∂mu)^2 -
          (uHat e c d a : ℝ)^2| := by
    simpa only [abs_neg, sub_eq_add_neg] using
      abs_add_le
        ((∫ g : G, (F b0 hb0 f0 e a g)^2 ∂mu) -
          (sHat e c d a : ℝ))
        (-((∫ g : G, F b0 hb0 f0 e a g ∂mu)^2 -
          (uHat e c d a : ℝ)^2))
  exact hTriangle.trans (add_le_add hSecond hSquare)

/-- FINITE rational Haar quadrature induces the actual AFI
coefficient-and-variance certificate, with all error evidence proved. -/
def p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c where
  coefficientCenter := fun a j => cHat e c d a j
  coefficientError := fun a j => cErr e c d a j
  varianceCenter := fun a => vHat e c d a
  varianceError := fun a => vErr e c d a
  hThetaLo := d.hThetaLo
  hCoefficientError_nonneg := by
    intro a ha j
    exact p4Q2PZ37AFJ_HaarTotalError_nonneg d.partition
      (d.coefficientSample a j) (d.coefficientOsc a j)
      (d.hCoefficientOsc_nonneg a ha j)
  hVarianceError_nonneg := by
    intro a ha
    exact p4Q2PZ37AFJ_originalVarianceError_nonneg H e c d a ha
  hCoefficientAccuracy := by
    intro a ha j
    exact p4Q2PZ37AFJ_originalCoefficient_accuracy H e c d a ha j
  hVarianceAccuracy := by
    intro a ha
    exact p4Q2PZ37AFJ_originalVariance_accuracy H e c d a ha

/-- Authentic AFH center selection, directly from finite cellwise
original receiver/Haar proofs via AFJ and AFI. -/
def p4Q2PZ37AFJ_originalQuadratureShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c) :
    Finset Pair :=
  p4Q2PZ37AFI_derivedOriginalShellCenters H e c
    (p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate H e c d)

/-- Every accepted genuine finite quadrature shell center has the
unchanged original Wilson/Perron physical gap signs, not proxy signs. -/
theorem p4Q2PZ37AFJ_originalQuadratureShellCenter_trueSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFJ_originalQuadratureShellCenters H e c d) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi :=
  p4Q2PZ37AFI_derivedCenter_trueOriginalSigns H e c
    (p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate H e c d) a ha

/-- If a genuine finite-cell quadrature center actually passes the
strict test, the ORIGINAL Haar shell has strictly positive mass. -/
theorem p4Q2PZ37AFJ_originalQuadratureShellCenter_positiveHaar
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFJ_originalQuadratureShellCenters H e c d) :
    0 < Measure.real outer (Shell e lo hi) := by
  have hFloor := p4Q2PZ37AFH_intervalCenter_floor_le_shellMass H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c
      (p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate H e c d)) a ha
  exact (p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR).trans_le hFloor

/-- A separated packing of verified genuine finite-cell quadrature
centers gives the unchanged AEA Haar mass lower bound. -/
theorem p4Q2PZ37AFJ_originalQuadraturePacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c) :
    ∃ t : Finset Pair,
      t ⊆ p4Q2PZ37AFJ_originalQuadratureShellCenters H e c d ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b) ∧
      (∀ a ∈ p4Q2PZ37AFJ_originalQuadratureShellCenters H e c d,
        ∃ b ∈ t, D a b < 2 * c.r) ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFI_derivedOriginalPacking_exists H e c
    (p4Q2PZ37AFJ_toOriginalCoefficientVarianceCertificate H e c d)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_eq_onCell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_pointwise_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_weightError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_integral_error_of_cells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarTotalError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalCoefficient_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalMean_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalSecond_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalVarianceError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalVariance_moment_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalVariance_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalQuadratureShellCenter_trueSigns
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalQuadratureShellCenter_positiveHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalQuadraturePacking_exists
