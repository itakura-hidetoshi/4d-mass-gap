import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatial24CellHaarProductV5_PZ37AGD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGE — original continuous spatial-Haar signed transfer samples

AGC's original signed transfer integrand is defined by evaluating an L2
representative; this value is NOT pointwise equal to its continuous Wilson
representative everywhere. AFZ proves equality only Haar almost everywhere.

AGE explicitly preserves that distinction. It identifies the genuine
signed transfer integral with its actual continuous centered Wilson
representative, then uses AGD's true 24^L spatial product Haar partition
and original AFQ center values to build rational quadrature samples.
Each true original continuous center value is enclosed by a (possibly
noncomputable) rational q_i with error 1/64. With a proved local
oscillation budget epsilon over the TRUE original spatial product cells:

  |t_H(B) - sum_i q_i*w_i|
    <= epsilon + 1/64 + sum_i |q_i| delta_i.

AGD supplies the true spatial-Haar mass enclosure w_i +/- delta_i.
The only remaining local physical input is the original continuous
integrand oscillation; this module does NOT assert that arbitrary L2
representatives agree pointwise, or that oscillation budgets have been
numerically certified. The finite center table is selected by rational
density from true physical values and is not a computed measurement.

No actual nonzero transfer sign, two-sign shell, volume-uniform coercivity,
Hamiltonian spectral gap, or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGE_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGE_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGE_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGE_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" =>
  decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "cells" => p4Q2PZ37AGD_toAGCOriginalHaarCells H
local notation "CellIndex" =>
  Fin (Fintype.card (p4Q2PZ37AGD_spatialGridIndex H))

local instance p4Q2PZ37AGE_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGE_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The actual original continuous centered Wilson/one-slab kernel
integrand; equality with the original L2 representative is only a.e. -/
def p4Q2PZ37AGE_originalContinuousIntegrand
    (B A : Cfg) : ℝ :=
  (p4Q2PZ37AFZ_originalCenteredContinuous H) A *
    (K A B - (1 + kFloor) / 2)

/-- Genuine Wilson action and true one-slab kernel are continuous.
The spatial continuous representative is not a new physical source. -/
theorem p4Q2PZ37AGE_originalContinuousIntegrand_continuous
    (B : Cfg) :
    Continuous (p4Q2PZ37AGE_originalContinuousIntegrand H B) := by
  have hSource :
      Continuous (fun A : Cfg =>
        (p4Q2PZ37AFZ_originalCenteredContinuous H) A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hKernel : Continuous (fun A : Cfg => K A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 b0).comp (continuous_id.prodMk continuous_const)
  unfold p4Q2PZ37AGE_originalContinuousIntegrand
  exact hSource.mul (hKernel.sub continuous_const)

/-- Do NOT conflate a Haar-L2 representative with its continuous version:
the true original integrands coincide only almost everywhere. -/
theorem p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous
    (B : Cfg) :
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand B) =ᵐ[muH]
      (p4Q2PZ37AGE_originalContinuousIntegrand H B) := by
  have hRep :
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH]
        (p4Q2PZ37AFZ_originalCenteredContinuous H) := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) (p4Q2PZ37AFZ_originalCenteredContinuous H)
  filter_upwards [hRep] with A hA
  change (f0 : Lp ℝ 2 muH) A * (K A B - (1 + kFloor) / 2) =
    (p4Q2PZ37AFZ_originalCenteredContinuous H) A *
      (K A B - (1 + kFloor) / 2)
  rw [hA]

/-- The original signed transfer is EXACTLY the Haar integral of this
continuous representative, without changing the physical observable. -/
theorem p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer
    (B : Cfg) :
    (∫ A : Cfg, p4Q2PZ37AGE_originalContinuousIntegrand H B A ∂muH) =
      t B := by
  rw [← p4Q2PZ37AGC_originalCenteredKernelIntegrand_integral B]
  exact integral_congr_ae
    (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H B).symm

/-- Use the actual AFQ SU(2) center at every original spatial link,
including for first-index cells whose designated center lies elsewhere. -/
def p4Q2PZ37AGE_spatialProductCenter
    (i : CellIndex) : Cfg :=
  fun e : Link =>
    p4Q2PZ37AFQ_originalCenters (p4Q2PZ37AGD_indexFromFin H i e)

/-- Every point in an original spatial product cell is within the proved
AFQ 4/5 chordal radius of its designated center on each link. -/
theorem p4Q2PZ37AGE_cell_perLink_chordalRadius
    (i : CellIndex) (A : Cfg)
    (hA : A ∈ cells.cell i) (e : Link) :
    p4Q2PZ37ADK_trueChordalDistance (A e)
      (p4Q2PZ37AGE_spatialProductCenter H i e) ≤ (4 / 5 : ℝ) := by
  have he : A e ∈
      p4Q2PZ37AFQ_cells (p4Q2PZ37AGD_indexFromFin H i e) := by
    exact (Set.mem_univ_pi.mp hA) e
  exact p4Q2PZ37AFQ_cells_chordalRadius
    (p4Q2PZ37AGD_indexFromFin H i e) (A e) he

/-- Exact genuine center integrand values are enclosed by rational
density with fixed error 1/64. This is a proof-carrying choice, not
an evaluated finite-volume numerical measurement. -/
noncomputable def p4Q2PZ37AGE_originalSpatialSample
    (B : Cfg) (i : CellIndex) : ℚ :=
  p4Q2PZ37AFN_rationalEnclosure
    (p4Q2PZ37AGE_originalContinuousIntegrand H B
      (p4Q2PZ37AGE_spatialProductCenter H i))
    (1 / 64) (by norm_num)

theorem p4Q2PZ37AGE_originalSpatialSample_accuracy
    (B : Cfg) (i : CellIndex) :
    |p4Q2PZ37AGE_originalContinuousIntegrand H B
        (p4Q2PZ37AGE_spatialProductCenter H i) -
      (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ)| ≤ (1 / 64 : ℝ) :=
  p4Q2PZ37AFN_rationalEnclosure_error
    (p4Q2PZ37AGE_originalContinuousIntegrand H B
      (p4Q2PZ37AGE_spatialProductCenter H i))
    (1 / 64) (by norm_num)

/-- Explicitly separates the STILL-UNRESOLVED local physical
oscillation bound from the already-certified Haar cell masses. -/
structure p4Q2PZ37AGE_originalSpatialOscillation
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) where
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  hOsc : ∀ i : Fin (Fintype.card (p4Q2PZ37AGD_spatialGridIndex H)),
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
    A ∈ (p4Q2PZ37AGD_toAGCOriginalHaarCells H).cell i →
    |p4Q2PZ37AGE_originalContinuousIntegrand H B A -
      p4Q2PZ37AGE_originalContinuousIntegrand H B
        (p4Q2PZ37AGE_spatialProductCenter H i)| ≤ epsilon

/-- A certified local physical oscillation plus exact true center
sampling gives a proof of cellwise rational enclosure, with no
pointwise equality assumption on arbitrary L2 representatives. -/
theorem p4Q2PZ37AGE_originalCellwiseSample_accuracy
    (B : Cfg)
    (cert : p4Q2PZ37AGE_originalSpatialOscillation H B)
    (i : CellIndex) (A : Cfg) (hA : A ∈ cells.cell i) :
    |p4Q2PZ37AGE_originalContinuousIntegrand H B A -
      (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ)| ≤
      cert.epsilon + (1 / 64 : ℝ) := by
  have hOsc := cert.hOsc i A hA
  have hSample := p4Q2PZ37AGE_originalSpatialSample_accuracy H B i
  calc
    |p4Q2PZ37AGE_originalContinuousIntegrand H B A -
        (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ)| =
      |(p4Q2PZ37AGE_originalContinuousIntegrand H B A -
          p4Q2PZ37AGE_originalContinuousIntegrand H B
            (p4Q2PZ37AGE_spatialProductCenter H i)) +
        (p4Q2PZ37AGE_originalContinuousIntegrand H B
            (p4Q2PZ37AGE_spatialProductCenter H i) -
          (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ))| := by
        congr 1
        ring
    _ ≤ |p4Q2PZ37AGE_originalContinuousIntegrand H B A -
          p4Q2PZ37AGE_originalContinuousIntegrand H B
            (p4Q2PZ37AGE_spatialProductCenter H i)| +
        |p4Q2PZ37AGE_originalContinuousIntegrand H B
            (p4Q2PZ37AGE_spatialProductCenter H i) -
          (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ)| :=
      abs_add_le _ _
    _ ≤ cert.epsilon + (1 / 64 : ℝ) := add_le_add hOsc hSample

/-- TRUE signed transfer Haar integral around a rational finite
AGD grid-center sum with the proved spatial Haar cell mass errors. -/
theorem p4Q2PZ37AGE_originalSignedTransfer_accuracy
    (B : Cfg)
    (cert : p4Q2PZ37AGE_originalSpatialOscillation H B) :
    |t B - (p4Q2PZ37AGC_HaarCenter cells
      (p4Q2PZ37AGE_originalSpatialSample H B) : ℝ)| ≤
      p4Q2PZ37AGC_HaarTotalError cells
        (p4Q2PZ37AGE_originalSpatialSample H B)
        (cert.epsilon + (1 / 64 : ℝ)) := by
  have hInt :
      Integrable (p4Q2PZ37AGE_originalContinuousIntegrand H B) muH :=
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable B).congr
      (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H B)
  have hLoc : ∀ i : Fin cells.n, ∀ A : Cfg,
      A ∈ cells.cell i →
      |p4Q2PZ37AGE_originalContinuousIntegrand H B A -
        (p4Q2PZ37AGE_originalSpatialSample H B i : ℝ)| ≤
          cert.epsilon + (1 / 64 : ℝ) := by
    intro i A hA
    exact p4Q2PZ37AGE_originalCellwiseSample_accuracy H B cert i A hA
  have h := p4Q2PZ37AGC_integral_error_of_cells cells
      (p4Q2PZ37AGE_originalContinuousIntegrand H B)
      (p4Q2PZ37AGE_originalSpatialSample H B)
      (cert.epsilon + (1 / 64 : ℝ)) hInt hLoc
  rw [p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H B] at h
  exact h

/-- Preserve the AGA rationalBall meaning: an actual RATIONAL radius
must cover the REAL finite-cell oscillation/weight error budget. -/
def p4Q2PZ37AGE_originalSignedTransferBall
    (B : Cfg)
    (cert : p4Q2PZ37AGE_originalSpatialOscillation H B)
    (radius : ℚ) (hRadius0 : 0 ≤ radius)
    (hRadius : p4Q2PZ37AGC_HaarTotalError cells
      (p4Q2PZ37AGE_originalSpatialSample H B)
      (cert.epsilon + (1 / 64 : ℝ)) ≤ (radius : ℝ)) :
    p4Q2PZ37AGA_rationalBall (t B) where
  sample := p4Q2PZ37AGC_HaarCenter cells
    (p4Q2PZ37AGE_originalSpatialSample H B)
  radius := radius
  radius_nonneg := hRadius0
  hContains := (p4Q2PZ37AGE_originalSignedTransfer_accuracy H B cert).trans hRadius

/-- Positive original transfer sign is a conditional, checkable
rational inequality; neither signed witness nor shell is invented. -/
theorem p4Q2PZ37AGE_originalSignedTransfer_positive
    (B : Cfg)
    (cert : p4Q2PZ37AGE_originalSpatialOscillation H B)
    (radius : ℚ) (hRadius0 : 0 ≤ radius)
    (hRadius : p4Q2PZ37AGC_HaarTotalError cells
      (p4Q2PZ37AGE_originalSpatialSample H B)
      (cert.epsilon + (1 / 64 : ℝ)) ≤ (radius : ℝ))
    (hPos : radius <
      p4Q2PZ37AGC_HaarCenter cells
        (p4Q2PZ37AGE_originalSpatialSample H B)) :
    0 < t B :=
  p4Q2PZ37AGA_rationalBall_positive
    (p4Q2PZ37AGE_originalSignedTransferBall H B cert radius hRadius0 hRadius) hPos

/-- Negative signed original transfer under the opposite strict
rational separation, still without a numerical physical assertion. -/
theorem p4Q2PZ37AGE_originalSignedTransfer_negative
    (B : Cfg)
    (cert : p4Q2PZ37AGE_originalSpatialOscillation H B)
    (radius : ℚ) (hRadius0 : 0 ≤ radius)
    (hRadius : p4Q2PZ37AGC_HaarTotalError cells
      (p4Q2PZ37AGE_originalSpatialSample H B)
      (cert.epsilon + (1 / 64 : ℝ)) ≤ (radius : ℝ))
    (hNeg : p4Q2PZ37AGC_HaarCenter cells
      (p4Q2PZ37AGE_originalSpatialSample H B) < -radius) :
    t B < 0 :=
  p4Q2PZ37AGA_rationalBall_negative
    (p4Q2PZ37AGE_originalSignedTransferBall H B cert radius hRadius0 hRadius) hNeg

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalContinuousIntegrand_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_cell_perLink_chordalRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalSpatialSample_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalCellwiseSample_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalSignedTransfer_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalSignedTransferBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalSignedTransfer_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGE_originalSignedTransfer_negative
