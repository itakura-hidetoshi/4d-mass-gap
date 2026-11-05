import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredTransferKernelCancellationV5_PZ37AGB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGC — finite spatial Haar quadrature with signed rational centers

This append-only module extends the already proved AFJ single-SU(2)-link
Haar partition quadrature to the full ORIGINAL spatial Haar configuration.
For the actual ZW Gauss-law centered source f_H and original one-slab
Wilson kernel K_H, AGB proved

  t_H(B) = ∫ f_H(A) * (K_H(A,B) - (1 + k_H)/2) dmu_H(A).

AGC builds a FINITE rational quadrature center for this exact signed
integrand over a genuine measurable spatial-Haar partition. It proves

  |t_H(B) - sum_i q_i*w_i| <= eps + sum_i |q_i|*dw_i.

The q_i and w_i are rational, the dw_i and pointwise eps are explicitly
certified against the original Haar measure and genuine integrand.
A rational radius bounding the displayed REAL error yields an AGA
rationalBall and AFV verifiedInterval with NONZERO centers when the
verified table actually produces such a nonzero rational value.

No unverified sample is asserted. Both positive and negative genuine
transfer signs are conditional on the rational center exceeding its
certified radius. There is no two-sign physical shell, volume-uniform
coercivity, Hamiltonian spectral gap, or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable {H : ℕ}
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" =>
  decomposableOneSliceTransferIntegral H 2 b0 f0

local instance p4Q2PZ37AGC_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGC_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The same AFJ partition calculus, now for the full original spatial
configuration and its ORIGINAL product Haar probability. -/
structure p4Q2PZ37AGC_originalHaarCells (H : ℕ) where
  n : ℕ
  cell : Fin n → Set
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
  hMeas : ∀ i, MeasurableSet (cell i)
  hPartition :
    ∀ g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ∃ i : Fin n, g ∈ cell i ∧ ∀ j : Fin n, g ∈ cell j → j = i
  weight : Fin n → ℚ
  weightError : Fin n → ℝ
  hWeightError_nonneg : ∀ i, 0 ≤ weightError i
  hWeightAccuracy : ∀ i,
    |Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (cell i) - (weight i : ℝ)| ≤ weightError i

/-- A truly finite simple function, integrated against original Haar. -/
def p4Q2PZ37AGC_HaarStep
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) (g : Cfg) : ℝ :=
  ∑ i : Fin p.n, (p.cell i).indicator (fun _ : Cfg => (q i : ℝ)) g

/-- Rational finite weighted estimate, with no floating-point casts. -/
def p4Q2PZ37AGC_HaarCenter
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) : ℚ :=
  ∑ i : Fin p.n, q i * p.weight i

/-- Error from certified rational mass approximations only. -/
def p4Q2PZ37AGC_HaarWeightError
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) : ℝ :=
  ∑ i : Fin p.n, |(q i : ℝ)| * p.weightError i

/-- Explicit total error budget including cell oscillation. -/
def p4Q2PZ37AGC_HaarTotalError
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) (eps : ℝ) : ℝ :=
  eps + p4Q2PZ37AGC_HaarWeightError p q

/-- Exactly one cell contributes at any point of the genuine Haar
partition. This prevents double counting of overlapping cells. -/
theorem p4Q2PZ37AGC_HaarStep_eq_onCell
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) (i : Fin p.n) (g : Cfg)
    (hi : g ∈ p.cell i) :
    p4Q2PZ37AGC_HaarStep p q g = (q i : ℝ) := by
  classical
  have hUnique := p.hPartition g
  obtain ⟨k, hk, hOnly⟩ := hUnique
  have hI : i = k := hOnly i hi
  have hNot (j : Fin p.n) (hj : j ≠ i) : g ∉ p.cell j := by
    intro h
    have heq : j = i := (hOnly j h).trans hI.symm
    exact hj heq
  unfold p4Q2PZ37AGC_HaarStep
  calc
    (∑ j : Fin p.n, (p.cell j).indicator (fun _ : Cfg => (q j : ℝ)) g) =
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
theorem p4Q2PZ37AGC_HaarStep_pointwise_bound
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) (f : Cfg → ℝ) (eps : ℝ)
    (hLocal : ∀ i (g : Cfg), g ∈ p.cell i →
      |f g - (q i : ℝ)| ≤ eps) :
    ∀ g : Cfg, |f g - p4Q2PZ37AGC_HaarStep p q g| ≤ eps := by
  intro g
  obtain ⟨i, hi, _⟩ := p.hPartition g
  rw [p4Q2PZ37AGC_HaarStep_eq_onCell p q i g hi]
  exact hLocal i g hi

/-- Each genuine measurable Haar step is integrable on the
unchanged normalized Haar probability. -/
theorem p4Q2PZ37AGC_HaarStep_integrable
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) :
    Integrable (p4Q2PZ37AGC_HaarStep p q) muH := by
  unfold p4Q2PZ37AGC_HaarStep
  apply integrable_finset_sum
  intro i _
  exact (integrable_const (q i : ℝ)).indicator (p.hMeas i)

/-- Exact finite indicator integration uses ORIGINAL normalized Haar,
not the rational approximate weights. -/
theorem p4Q2PZ37AGC_HaarStep_integral
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) :
    (∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH) =
      ∑ i : Fin p.n, Measure.real muH (p.cell i) * (q i : ℝ) := by
  unfold p4Q2PZ37AGC_HaarStep
  rw [integral_finset_sum Finset.univ
    (fun i _ => (integrable_const (q i : ℝ)).indicator (p.hMeas i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const (q i : ℝ) (p.hMeas i), smul_eq_mul]

/-- Finite rational-weight error bound for genuine Haar step integrals. -/
theorem p4Q2PZ37AGC_HaarStep_weightError
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) :
    |(∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH) -
      (p4Q2PZ37AGC_HaarCenter p q : ℝ)| ≤
        p4Q2PZ37AGC_HaarWeightError p q := by
  rw [p4Q2PZ37AGC_HaarStep_integral]
  have hCast : (p4Q2PZ37AGC_HaarCenter p q : ℝ) =
      ∑ i : Fin p.n, (q i : ℝ) * (p.weight i : ℝ) := by
    simp [p4Q2PZ37AGC_HaarCenter]
  rw [hCast]
  have hTerm (i : Fin p.n) :
      |Measure.real muH (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ)| ≤
            |(q i : ℝ)| * p.weightError i := by
    have h := p.hWeightAccuracy i
    have hEq : Measure.real muH (p.cell i) * (q i : ℝ) -
        (q i : ℝ) * (p.weight i : ℝ) =
          (q i : ℝ) * (Measure.real muH (p.cell i) - (p.weight i : ℝ)) := by
      ring
    rw [hEq, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  calc
    |(∑ i : Fin p.n, Measure.real muH (p.cell i) * (q i : ℝ)) -
      (∑ i : Fin p.n, (q i : ℝ) * (p.weight i : ℝ))| =
      |∑ i : Fin p.n,
        (Measure.real muH (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin p.n,
        |Measure.real muH (p.cell i) * (q i : ℝ) -
          (q i : ℝ) * (p.weight i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ p4Q2PZ37AGC_HaarWeightError p q := by
      unfold p4Q2PZ37AGC_HaarWeightError
      exact Finset.sum_le_sum (fun i _ => hTerm i)

/-- A single total error bound from FINITE, cellwise, rational data
and certified true Haar cell masses. Genuine integrands stay unchanged. -/
theorem p4Q2PZ37AGC_integral_error_of_cells
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (f : Cfg → ℝ) (q : Fin p.n → ℚ) (eps : ℝ)
    (hf : Integrable f muH)
    (hLocal : ∀ i (g : Cfg), g ∈ p.cell i →
      |f g - (q i : ℝ)| ≤ eps) :
    |(∫ g : Cfg, f g ∂muH) -
      (p4Q2PZ37AGC_HaarCenter p q : ℝ)| ≤
        p4Q2PZ37AGC_HaarTotalError p q eps := by
  have hF : Integrable f muH := hf
  have hStep := p4Q2PZ37AGC_HaarStep_integrable p q
  have hPoint : |(∫ g : Cfg, f g ∂muH) -
      (∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH)| ≤ eps := by
    have hNorm := norm_integral_le_of_norm_le_const
      (μ := muH) (f := fun g : Cfg => f g - p4Q2PZ37AGC_HaarStep p q g)
      (C := eps) (Filter.Eventually.of_forall (fun g : Cfg => by
        simpa only [Real.norm_eq_abs] using
          p4Q2PZ37AGC_HaarStep_pointwise_bound p q f eps hLocal g))
    rw [← integral_sub hF hStep]
    simpa [Real.norm_eq_abs] using hNorm
  have hWeight := p4Q2PZ37AGC_HaarStep_weightError p q
  calc
    |(∫ g : Cfg, f g ∂muH) -
        (p4Q2PZ37AGC_HaarCenter p q : ℝ)| =
      |((∫ g : Cfg, f g ∂muH) -
          (∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH)) +
        ((∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH) -
          (p4Q2PZ37AGC_HaarCenter p q : ℝ))| := by
        congr 1
        ring
    _ ≤ |(∫ g : Cfg, f g ∂muH) -
          (∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH)| +
        |(∫ g : Cfg, p4Q2PZ37AGC_HaarStep p q g ∂muH) -
          (p4Q2PZ37AGC_HaarCenter p q : ℝ)| :=
      abs_add_le _ _
    _ ≤ p4Q2PZ37AGC_HaarTotalError p q eps := by
      unfold p4Q2PZ37AGC_HaarTotalError
      exact add_le_add hPoint hWeight

/-- Finite error budgets are nonnegative whenever the cellwise
oscillation budget is nonnegative. -/
theorem p4Q2PZ37AGC_HaarTotalError_nonneg
    (p : p4Q2PZ37AGC_originalHaarCells H)
    (q : Fin p.n → ℚ) (eps : ℝ) (hEps : 0 ≤ eps) :
    0 ≤ p4Q2PZ37AGC_HaarTotalError p q eps := by
  unfold p4Q2PZ37AGC_HaarTotalError p4Q2PZ37AGC_HaarWeightError
  apply add_nonneg hEps
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (abs_nonneg _) (p.hWeightError_nonneg i)


/-- Genuine centered-kernel integrand; no source or Wilson kernel change. -/
def p4Q2PZ37AGC_originalCenteredKernelIntegrand
    (B A : Cfg) : ℝ :=
  (f0 : Lp ℝ 2 muH) A * (K A B - (1 + kFloor) / 2)

/-- The true centered-kernel integrand is integrable because the original
signed transfer integrand and the centered source are integrable. -/
theorem p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable
    (B : Cfg) :
    Integrable (p4Q2PZ37AGC_originalCenteredKernelIntegrand B) muH := by
  have hf : Integrable (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) muH :=
    (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hu : Integrable (fun A : Cfg => (f0 : Lp ℝ 2 muH) A * K A B) muH :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) b0 hb0 (f0 : Lp ℝ 2 muH) B
  have hv : Integrable
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A * ((1 + kFloor) / 2)) muH :=
    hf.mul_const ((1 + kFloor) / 2)
  have hEq :
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A * (K A B - (1 + kFloor) / 2)) =
      (fun A : Cfg =>
        (f0 : Lp ℝ 2 muH) A * K A B -
        (f0 : Lp ℝ 2 muH) A * ((1 + kFloor) / 2)) := by
    funext A
    ring
  unfold p4Q2PZ37AGC_originalCenteredKernelIntegrand
  rw [hEq]
  exact hu.sub hv

/-- AGB's literal spatial-Haar cancellation transports the genuine
signed transfer to this centered-kernel integrand. -/
theorem p4Q2PZ37AGC_originalCenteredKernelIntegrand_integral
    (B : Cfg) :
    (∫ A : Cfg, p4Q2PZ37AGC_originalCenteredKernelIntegrand B A ∂muH) =
      t B := by
  change (∫ A : Cfg, (f0 : Lp ℝ 2 muH) A *
    (K A B - (1 + kFloor) / 2) ∂muH) = t B
  exact (p4Q2PZ37AGB_originalTransfer_eq_kernelCenteredIntegral H B ((1 + kFloor) / 2)).symm

/-- Concrete rational spatial-Haar quadrature table with exact
cellwise *physical* integrand bounds and certified original Haar masses.
A nonzero center is allowed, but not presumed. -/
structure p4Q2PZ37AGC_originalSignedTransferQuadrature
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) where
  cells : p4Q2PZ37AGC_originalHaarCells H
  samples : Fin cells.n → ℚ
  eps : ℝ
  eps_nonneg : 0 ≤ eps
  hCell : ∀ i (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2),
    A ∈ cells.cell i →
      |p4Q2PZ37AGC_originalCenteredKernelIntegrand B A -
        (samples i : ℝ)| ≤ eps
  radius : ℚ
  radius_nonneg : 0 ≤ radius
  hRadius : p4Q2PZ37AGC_HaarTotalError cells samples eps ≤ (radius : ℝ)

/-- Every certified finite spatial-Haar table bounds the original signed
transfer integral around an explicit rational center. -/
theorem p4Q2PZ37AGC_originalSignedTransfer_accuracy
    (B : Cfg)
    (c : p4Q2PZ37AGC_originalSignedTransferQuadrature H B) :
    |t B - (p4Q2PZ37AGC_HaarCenter c.cells c.samples : ℝ)| ≤
      (c.radius : ℝ) := by
  have h := p4Q2PZ37AGC_integral_error_of_cells c.cells
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand B)
    c.samples c.eps
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable B)
    c.hCell
  rw [p4Q2PZ37AGC_originalCenteredKernelIntegrand_integral B] at h
  exact h.trans c.hRadius

/-- Proof-carrying rational center/radius for the TRUE signed transfer.
Unlike AGB's unconditional radius, the center need not be zero. -/
def p4Q2PZ37AGC_originalSignedTransferRationalBall
    (B : Cfg)
    (c : p4Q2PZ37AGC_originalSignedTransferQuadrature H B) :
    p4Q2PZ37AGA_rationalBall (t B) where
  sample := p4Q2PZ37AGC_HaarCenter c.cells c.samples
  radius := c.radius
  radius_nonneg := c.radius_nonneg
  hContains := p4Q2PZ37AGC_originalSignedTransfer_accuracy B c

/-- Reuse the existing AFV verified rational interval without weakening
its meaning or inventing numerical integral values. -/
def p4Q2PZ37AGC_originalSignedTransferInterval
    (B : Cfg)
    (c : p4Q2PZ37AGC_originalSignedTransferQuadrature H B) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGA_toVerifiedInterval
    (p4Q2PZ37AGC_originalSignedTransferRationalBall B c)

/-- A certified positive rational center beyond its radius yields the
actual positive signed transfer value. -/
theorem p4Q2PZ37AGC_originalSignedTransfer_positive
    (B : Cfg)
    (c : p4Q2PZ37AGC_originalSignedTransferQuadrature H B)
    (h : c.radius < p4Q2PZ37AGC_HaarCenter c.cells c.samples) :
    0 < t B :=
  p4Q2PZ37AGA_rationalBall_positive
    (p4Q2PZ37AGC_originalSignedTransferRationalBall B c) h

/-- Corresponding rigorous original negative transfer certificate. -/
theorem p4Q2PZ37AGC_originalSignedTransfer_negative
    (B : Cfg)
    (c : p4Q2PZ37AGC_originalSignedTransferQuadrature H B)
    (h : p4Q2PZ37AGC_HaarCenter c.cells c.samples < -c.radius) :
    t B < 0 :=
  p4Q2PZ37AGA_rationalBall_negative
    (p4Q2PZ37AGC_originalSignedTransferRationalBall B c) h

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarStep_eq_onCell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarStep_pointwise_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarStep_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarStep_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarStep_weightError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_integral_error_of_cells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_HaarTotalError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalCenteredKernelIntegrand_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalSignedTransfer_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalSignedTransferRationalBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalSignedTransferInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalSignedTransfer_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGC_originalSignedTransfer_negative
