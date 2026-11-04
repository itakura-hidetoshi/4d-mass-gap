import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimalMomentHaarV5_PZ37AFT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFU — genuine centered Haar quadrature and original physical samples

AFT proved the optimal second-moment Haar upper bound on the SAME
original SU(2) 24-cell Borel partition, with fixed rational weights 1/24
and individual mass-error bound δ = 13219/42744.

AFU exploits a stronger invariant than individual cell enclosure:
both the true Haar cell masses and the fixed rational weights sum to ONE.
Hence the 24 errors have exactly zero sum. The constant mode of any
rational sample table cancels, and its genuine Haar integral error obeys

  |sum_i (μ(C_i) - 1/24) q_i| <= δ * sum_i |q_i - s|,

for ANY rational shift s. In particular a constant nonzero table has
EXACTLY ZERO Haar mass-weight error. Choosing s = 0 reproduces AFT;
the min of the two bounds never weakens AFT.

These bounds are transferred to the original AFF/AFM→AFJ physical
receiver's genuine four-mode coefficient, mean and second moment.
AFN rational density also supplies a typed arbitrarily-accurate
24-center pointwise sample (noncomputable Classical.choose), with
fixed AFT weights, without extra physical assumptions.

IMPORTANT: no concrete FF numerical sample, verified interval
evaluation, nonempty genuine two-sign shell, volume-uniform coercivity,
Hamiltonian spectral gap or continuum 4D Yang–Mills gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters
local notation "partitionAFT" => p4Q2PZ37AFT_originalOptimalHaarCells
local notation "δ" => (13219 / 42744 : ℝ)

local instance p4Q2PZ37AFU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFU_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The sum of the original 24 true Borel cell masses is ONE,
not merely at most one. The proof uses the existing AFJ exact
simple-function integral and the actual AFQ partition. -/
theorem p4Q2PZ37AFU_original24CellHaarMass_sum_one :
    (∑ i : Fin (Fintype.card Grid),
      Measure.real mu (p4Q2PZ37AFQ_cells i)) = (1 : ℝ) := by
  let p : GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells :=
    partitionAFT
  have hPoint (g : G) :
      GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
        p (fun _ => (1 : ℚ)) g = 1 := by
    obtain ⟨i, hi, _⟩ := p.hPartition g
    simpa only [Rat.cast_one] using
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_eq_onCell
        p (fun _ => (1 : ℚ)) i g hi)
  have hIntegral :
      (∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
        p (fun _ => (1 : ℚ)) g ∂mu) = (1 : ℝ) := by
    calc
      (∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
        p (fun _ => (1 : ℚ)) g ∂mu) =
          (∫ _g : G, (1 : ℝ) ∂mu) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hPoint
      _ = 1 := by simp
  rw [GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_integral
    p (fun _ => (1 : ℚ))] at hIntegral
  simp only [Rat.cast_one, mul_one] at hIntegral
  change (∑ i : Fin (Fintype.card Grid),
    Measure.real mu (p4Q2PZ37AFQ_cells i)) = (1 : ℝ) at hIntegral
  exact hIntegral

theorem p4Q2PZ37AFU_original24FixedWeights_sum_one :
    (∑ i : Fin (Fintype.card Grid),
      (p4Q2PZ37AFR_fixedWeight i : ℝ)) = (1 : ℝ) := by
  exact_mod_cast p4Q2PZ37AFR_fixedWeight_sum_one

/-- Exact annihilation of the constant mode by the normalized
genuine Haar-minus-rational quadrature functional. -/
theorem p4Q2PZ37AFU_original24MassDeviation_sum_zero :
    (∑ i : Fin (Fintype.card Grid),
      (Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ))) = 0 := by
  rw [Finset.sum_sub_distrib,
    p4Q2PZ37AFU_original24CellHaarMass_sum_one,
    p4Q2PZ37AFU_original24FixedWeights_sum_one]
  ring

/-- Error of a rational table after subtracting ANY rational
constant mode, on AFT's verified 24 genuinely measured cells. -/
def p4Q2PZ37AFU_centeredHaarWeightError
    (q : Fin (Fintype.card Grid) → ℚ) (s : ℚ) : ℝ :=
  ∑ i : Fin (Fintype.card Grid), |((q i - s : ℚ) : ℝ)| * δ

theorem p4Q2PZ37AFU_centeredHaarWeightError_nonneg
    (q : Fin (Fintype.card Grid) → ℚ) (s : ℚ) :
    0 ≤ p4Q2PZ37AFU_centeredHaarWeightError q s := by
  unfold p4Q2PZ37AFU_centeredHaarWeightError
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (abs_nonneg _) (by norm_num)

theorem p4Q2PZ37AFU_centeredHaarWeightError_zeroShift
    (q : Fin (Fintype.card Grid) → ℚ) :
    p4Q2PZ37AFU_centeredHaarWeightError q 0 =
      GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarWeightError partitionAFT q := by
  simp [p4Q2PZ37AFU_centeredHaarWeightError,
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarWeightError,
    p4Q2PZ37AFT_originalOptimalHaarCells]

theorem p4Q2PZ37AFU_centeredHaarWeightError_constant_zero (s : ℚ) :
    p4Q2PZ37AFU_centeredHaarWeightError (fun _ => s) s = 0 := by
  simp [p4Q2PZ37AFU_centeredHaarWeightError]

/-- Improved genuine AFJ Haar step error; no independent-Haar model.
The identity uses the EXACT sum of original mass deviations = zero. -/
theorem p4Q2PZ37AFU_originalHaarStep_centeredWeightError
    (q : Fin (Fintype.card Grid) → ℚ) (s : ℚ) :
    |(∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
      partitionAFT q g ∂mu) -
        (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
          partitionAFT q : ℝ)| ≤
      p4Q2PZ37AFU_centeredHaarWeightError q s := by
  rw [GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_integral
    partitionAFT q]
  have hCast :
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
          partitionAFT q : ℝ) =
        ∑ i : Fin (Fintype.card Grid),
          (q i : ℝ) * (p4Q2PZ37AFR_fixedWeight i : ℝ) := by
    change
      ((∑ i : Fin (Fintype.card Grid),
        q i * p4Q2PZ37AFR_fixedWeight i : ℚ) : ℝ) = _
    push_cast
    rfl
  rw [hCast]
  change
    |(∑ i : Fin (Fintype.card Grid),
      Measure.real mu (p4Q2PZ37AFQ_cells i) * (q i : ℝ)) -
       (∑ i : Fin (Fintype.card Grid),
        (q i : ℝ) * (p4Q2PZ37AFR_fixedWeight i : ℝ))| ≤
          p4Q2PZ37AFU_centeredHaarWeightError q s
  have hDev := p4Q2PZ37AFU_original24MassDeviation_sum_zero
  have hShift :
      (∑ i : Fin (Fintype.card Grid),
        (Measure.real mu (p4Q2PZ37AFQ_cells i) -
          (p4Q2PZ37AFR_fixedWeight i : ℝ)) * (s : ℝ)) = 0 := by
    calc
      _ = (∑ i : Fin (Fintype.card Grid),
        (Measure.real mu (p4Q2PZ37AFQ_cells i) -
          (p4Q2PZ37AFR_fixedWeight i : ℝ))) * (s : ℝ) := by
          rw [Finset.sum_mul]
      _ = 0 := by rw [hDev]; ring
  have hRewrite :
      (∑ i : Fin (Fintype.card Grid),
        Measure.real mu (p4Q2PZ37AFQ_cells i) * (q i : ℝ)) -
        (∑ i : Fin (Fintype.card Grid),
          (q i : ℝ) * (p4Q2PZ37AFR_fixedWeight i : ℝ)) =
      ∑ i : Fin (Fintype.card Grid),
        (Measure.real mu (p4Q2PZ37AFQ_cells i) -
          (p4Q2PZ37AFR_fixedWeight i : ℝ)) *
            ((q i - s : ℚ) : ℝ) := by
    calc
      _ = ∑ i : Fin (Fintype.card Grid),
        (Measure.real mu (p4Q2PZ37AFQ_cells i) -
          (p4Q2PZ37AFR_fixedWeight i : ℝ)) * (q i : ℝ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = ∑ i : Fin (Fintype.card Grid),
        ((Measure.real mu (p4Q2PZ37AFQ_cells i) -
            (p4Q2PZ37AFR_fixedWeight i : ℝ)) * (q i : ℝ) -
         (Measure.real mu (p4Q2PZ37AFQ_cells i) -
            (p4Q2PZ37AFR_fixedWeight i : ℝ)) * (s : ℝ)) := by
          rw [Finset.sum_sub_distrib, hShift, sub_zero]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          push_cast
          ring
  rw [hRewrite]
  have hTerm (i : Fin (Fintype.card Grid)) :
      |(Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ)) * ((q i - s : ℚ) : ℝ)| ≤
        |((q i - s : ℚ) : ℝ)| * δ := by
    rw [abs_mul]
    calc
      |Measure.real mu (p4Q2PZ37AFQ_cells i) -
        (p4Q2PZ37AFR_fixedWeight i : ℝ)| *
        |((q i - s : ℚ) : ℝ)| ≤
          δ * |((q i - s : ℚ) : ℝ)| :=
        mul_le_mul_of_nonneg_right
          (p4Q2PZ37AFT_fixedWeight_accuracy i) (abs_nonneg _)
      _ = |((q i - s : ℚ) : ℝ)| * δ := by ring
  calc
    |∑ i : Fin (Fintype.card Grid),
        (Measure.real mu (p4Q2PZ37AFQ_cells i) -
          (p4Q2PZ37AFR_fixedWeight i : ℝ)) *
            ((q i - s : ℚ) : ℝ)| ≤
        ∑ i : Fin (Fintype.card Grid),
          |(Measure.real mu (p4Q2PZ37AFQ_cells i) -
            (p4Q2PZ37AFR_fixedWeight i : ℝ)) *
              ((q i - s : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ p4Q2PZ37AFU_centeredHaarWeightError q s := by
      unfold p4Q2PZ37AFU_centeredHaarWeightError
      exact Finset.sum_le_sum (fun i _ => hTerm i)

/-- The best of ordinary AFJ and constant-mode centered Haar-error
bounds NEVER becomes worse than the previous AFT certificate. -/
theorem p4Q2PZ37AFU_originalHaarStep_weightError_min
    (q : Fin (Fintype.card Grid) → ℚ) (s : ℚ) :
    |(∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
      partitionAFT q g ∂mu) -
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
        partitionAFT q : ℝ)| ≤
      min (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarWeightError
        partitionAFT q)
        (p4Q2PZ37AFU_centeredHaarWeightError q s) := by
  apply le_min
  · exact GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_weightError
      partitionAFT q
  · exact p4Q2PZ37AFU_originalHaarStep_centeredWeightError q s

/-- Truly centered finite rational quadrature for ANY continuous
integrand with a verified local cell oscillation bound. -/
theorem p4Q2PZ37AFU_originalIntegral_centeredAccuracy
    (f : G → ℝ) (q : Fin (Fintype.card Grid) → ℚ) (eps : ℝ)
    (hf : Continuous f)
    (hLocal : ∀ i (g : G), g ∈ p4Q2PZ37AFQ_cells i →
      |f g - (q i : ℝ)| ≤ eps) (s : ℚ) :
    |(∫ g : G, f g ∂mu) -
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
        partitionAFT q : ℝ)| ≤
      eps + p4Q2PZ37AFU_centeredHaarWeightError q s := by
  have hIntF : Integrable f mu :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntStep :=
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_integrable partitionAFT q
  have hPoint :
      |(∫ g : G, f g ∂mu) -
        (∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
          partitionAFT q g ∂mu)| ≤ eps := by
    have hNorm := norm_integral_le_of_norm_le_const
      (μ := mu)
      (f := fun g : G =>
        f g - GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
          partitionAFT q g)
      (C := eps) (Filter.Eventually.of_forall (fun g : G => by
        simpa only [Real.norm_eq_abs] using
          GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep_pointwise_bound
            partitionAFT q f eps hLocal g))
    rw [← integral_sub hIntF hIntStep]
    simpa [Real.norm_eq_abs] using hNorm
  have hWeight := p4Q2PZ37AFU_originalHaarStep_centeredWeightError q s
  calc
    |(∫ g : G, f g ∂mu) -
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
        partitionAFT q : ℝ)| =
      |((∫ g : G, f g ∂mu) -
        (∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
          partitionAFT q g ∂mu)) +
        ((∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
          partitionAFT q g ∂mu) -
          (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
            partitionAFT q : ℝ))| := by
            congr 1
            ring
    _ ≤ |(∫ g : G, f g ∂mu) -
      (∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
        partitionAFT q g ∂mu)| +
      |(∫ g : G, GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarStep
        partitionAFT q g ∂mu) -
        (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
          partitionAFT q : ℝ)| :=
      abs_add_le _ _
    _ ≤ eps + p4Q2PZ37AFU_centeredHaarWeightError q s :=
      add_le_add hPoint hWeight

theorem p4Q2PZ37AFU_originalIntegral_minAccuracy
    (f : G → ℝ) (q : Fin (Fintype.card Grid) → ℚ) (eps : ℝ)
    (hf : Continuous f)
    (hLocal : ∀ i (g : G), g ∈ p4Q2PZ37AFQ_cells i →
      |f g - (q i : ℝ)| ≤ eps) (s : ℚ) :
    |(∫ g : G, f g ∂mu) -
      (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarCenter
        partitionAFT q : ℝ)| ≤
      min (GroundStatePosteriorJoint.p4Q2PZ37AFJ_HaarTotalError
        partitionAFT q eps)
        (eps + p4Q2PZ37AFU_centeredHaarWeightError q s) := by
  apply le_min
  · exact GroundStatePosteriorJoint.p4Q2PZ37AFJ_integral_error_of_cells
      partitionAFT f q eps hf hLocal
  · exact p4Q2PZ37AFU_originalIntegral_centeredAccuracy
      f q eps hf hLocal s

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
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter

local instance p4Q2PZ37AFU_links : Fintype Link := Fintype.ofFinite _

/-- An arbitrary-accuracy rational enclosure for the SAME ORIGINAL FF
receiver at the FIXED 24 true centers, using AFN rational density.
It is noncomputable: the value is chosen using the unknown true FF
real number, not evaluated by a numerical interval algorithm. -/
noncomputable def p4Q2PZ37AFU_original24CenterPrecisionSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (eps : ℝ) (heps : 0 < eps) :
    p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c where
  meanSample := fun a i =>
    p4Q2PZ37AFN_rationalEnclosure
      (F e a (gridCenter i)) eps heps
  meanSampleError := fun _ => eps
  hMeanSampleError_nonneg := by intro a ha; exact heps.le
  hMeanSample := by
    intro a ha i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      (F e a (gridCenter i)) eps heps
  secondSample := fun a i =>
    p4Q2PZ37AFN_rationalEnclosure
      ((F e a (gridCenter i)) ^ 2) eps heps
  secondSampleError := fun _ => eps
  hSecondSampleError_nonneg := by intro a ha; exact heps.le
  hSecondSample := by
    intro a ha i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      ((F e a (gridCenter i)) ^ 2) eps heps
  coefficientSample := fun a j i =>
    p4Q2PZ37AFN_rationalEnclosure
      (F e a (gridCenter i) * phi j (gridCenter i)) eps heps
  coefficientSampleError := fun _ _ => eps
  hCoefficientSampleError_nonneg := by intro a ha j; exact heps.le
  hCoefficientSample := by
    intro a ha j i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      (F e a (gridCenter i) * phi j (gridCenter i)) eps heps

/-- The AFU pointwise rational precision is fed through the ORIGINAL
physical AFM→AFJ receiver, with the improved AFT fixed weights. -/
noncomputable def p4Q2PZ37AFU_originalPrecisionReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (eps : ℝ) (heps : 0 < eps) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFT_toOriginalReceiverQuadrature
    H e c hlo (p4Q2PZ37AFU_original24CenterPrecisionSamples H e c eps heps)

/-- Original AFM→AFI with arbitrary real sampling tolerance;
the certified partitions remain the fixed effective 24 Haar cells. -/
noncomputable def p4Q2PZ37AFU_originalPrecisionCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (eps : ℝ) (heps : 0 < eps) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFT_toOriginalCoefficientVarianceCertificate
    H e c hlo (p4Q2PZ37AFU_original24CenterPrecisionSamples H e c eps heps)

/-- A genuinely certified receiver coefficient with centered Haar
mass error; no external physical Lipschitz/character norm hypothesis. -/
theorem p4Q2PZ37AFU_originalCoefficient_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) (s : ℚ) :
    |p4Q2PZ37ACK_originalFourModeCoefficient H b0 hb0 e a j -
      (p4Q2PZ37AFJ_originalCoefficientCenter H e c
        (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d) a j : ℝ)| ≤
      (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d).coefficientOsc a j +
        p4Q2PZ37AFU_centeredHaarWeightError (d.coefficientSample a j) s := by
  let v := p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d
  have hF := p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a
  have hPhi := p4Q2PZ37ACK_fourModeCharacter_continuous j
  have hLocal : ∀ i (g : G), g ∈ p4Q2PZ37AFQ_cells i →
      |F e a g * phi j g - (d.coefficientSample a j i : ℝ)| ≤
        v.coefficientOsc a j := by
    intro i g hg
    exact v.hCoefficientLocal a ha j i g hg
  change
    |(∫ g : G, F e a g * phi j g ∂mu) -
      (p4Q2PZ37AFJ_HaarCenter partitionAFT
        (d.coefficientSample a j) : ℝ)| ≤
      v.coefficientOsc a j +
        p4Q2PZ37AFU_centeredHaarWeightError (d.coefficientSample a j) s
  exact p4Q2PZ37AFU_originalIntegral_centeredAccuracy
    (fun g : G => F e a g * phi j g)
    (d.coefficientSample a j) (v.coefficientOsc a j)
    (hF.mul hPhi) hLocal s

/-- Same constant-mode cancellation for the genuine original
receiver Haar mean. -/
theorem p4Q2PZ37AFU_originalMean_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (s : ℚ) :
    |(∫ g : G, F e a g ∂mu) -
      (p4Q2PZ37AFJ_originalMeanCenter H e c
        (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d) a : ℝ)| ≤
      (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d).meanOsc a +
        p4Q2PZ37AFU_centeredHaarWeightError (d.meanSample a) s := by
  let v := p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d
  have hLocal : ∀ i (g : G), g ∈ p4Q2PZ37AFQ_cells i →
      |F e a g - (d.meanSample a i : ℝ)| ≤ v.meanOsc a := by
    intro i g hg
    exact v.hMeanLocal a ha i g hg
  change
    |(∫ g : G, F e a g ∂mu) -
      (p4Q2PZ37AFJ_HaarCenter partitionAFT (d.meanSample a) : ℝ)| ≤
      v.meanOsc a + p4Q2PZ37AFU_centeredHaarWeightError (d.meanSample a) s
  exact p4Q2PZ37AFU_originalIntegral_centeredAccuracy
    (F e a) (d.meanSample a) (v.meanOsc a)
    (p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a)
    hLocal s

/-- Likewise the genuine FF second Haar moment, as used in
the original receiver variance, without changing physical sources. -/
theorem p4Q2PZ37AFU_originalSecond_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (s : ℚ) :
    |(∫ g : G, (F e a g)^2 ∂mu) -
      (p4Q2PZ37AFJ_originalSecondCenter H e c
        (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d) a : ℝ)| ≤
      (p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d).secondOsc a +
        p4Q2PZ37AFU_centeredHaarWeightError (d.secondSample a) s := by
  let v := p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo d
  have hLocal : ∀ i (g : G), g ∈ p4Q2PZ37AFQ_cells i →
      |(F e a g)^2 - (d.secondSample a i : ℝ)| ≤ v.secondOsc a := by
    intro i g hg
    exact v.hSecondLocal a ha i g hg
  change
    |(∫ g : G, (F e a g)^2 ∂mu) -
      (p4Q2PZ37AFJ_HaarCenter partitionAFT (d.secondSample a) : ℝ)| ≤
      v.secondOsc a + p4Q2PZ37AFU_centeredHaarWeightError (d.secondSample a) s
  exact p4Q2PZ37AFU_originalIntegral_centeredAccuracy
    (fun g : G => (F e a g)^2)
    (d.secondSample a) (v.secondOsc a)
    ((p4Q2PZ37ACK_centeredReceiver_continuous H b0 hb0 e a).pow 2)
    hLocal s

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_original24CellHaarMass_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_original24FixedWeights_sum_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_original24MassDeviation_sum_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_centeredHaarWeightError_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_centeredHaarWeightError_zeroShift
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_centeredHaarWeightError_constant_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_originalHaarStep_centeredWeightError
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_originalHaarStep_weightError_min
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_originalIntegral_centeredAccuracy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFU_originalIntegral_minAccuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFU_originalCoefficient_centeredAccuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFU_originalMean_centeredAccuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFU_originalSecond_centeredAccuracy
