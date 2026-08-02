import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct ENNReal

noncomputable section

local instance boundaryMarginalL2NeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalL2SecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real boundary `L²` for the reflection-fixed Haar law. -/
abbrev PeriodicHypercubicEvenBoundaryHaarL2
    (H N : ℕ) :=
  Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- Real boundary `L²` for the interacting Wilson boundary marginal. -/
abbrev PeriodicHypercubicEvenBoundaryMarginalL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :=
  Lp ℝ 2
    (periodicHypercubicEvenBoundaryMarginalMeasure
      H N hN beta hbeta)

/-- NNReal form of the interacting boundary marginal density. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalDensityNNReal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ≥0 :=
  ⟨periodicHypercubicEvenBoundaryVacuumMoment
      H N hN beta hbeta b ^ 2,
    sq_nonneg _⟩

/-- The NNReal and ENNReal forms of the marginal density agree. -/
theorem periodicHypercubicEvenBoundaryMarginalDensityNNReal_coe
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ((periodicHypercubicEvenBoundaryMarginalDensityNNReal
      H N hN beta hbeta b : ℝ≥0) : ℝ≥0∞) =
      periodicHypercubicEvenBoundaryMarginalDensity
        H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
  unfold periodicHypercubicEvenBoundaryMarginalDensity
  simp [ENNReal.ofReal_of_nonneg (sq_nonneg
    (periodicHypercubicEvenBoundaryVacuumMoment
      H N hN beta hbeta b))]

/-- The NNReal marginal density is measurable. -/
theorem periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
  exact
    ((periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).pow_const 2).subtype_mk _

/-- The marginal measure can be written with the NNReal density. -/
theorem periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryMarginalMeasure
      H N hN beta hbeta =
      (periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
        (fun b =>
          (periodicHypercubicEvenBoundaryMarginalDensityNNReal
            H N hN beta hbeta b : ℝ≥0∞)) := by
  unfold periodicHypercubicEvenBoundaryMarginalMeasure
  congr 1
  funext b
  exact
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_coe
      H N hN beta hbeta b).symm

/-- The reciprocal OS boundary vacuum wavefunction. -/
noncomputable def periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  (periodicHypercubicEvenBoundaryVacuumMoment
    H N hN beta hbeta b)⁻¹

/-- The reciprocal boundary-vacuum weight is measurable. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2Weight_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  exact
    (periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).inv₀

/-- The marginal density cancels the reciprocal boundary-vacuum weight
squared. -/
theorem periodicHypercubicEvenBoundaryMarginalDensityNNReal_mul_weight_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
      H N hN beta hbeta b : ℝ) *
        periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
          H N hN beta hbeta b ^ 2 = 1 := by
  unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  change
    periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b ^ 2 *
      (periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b)⁻¹ ^ 2 = 1
  field_simp [ne_of_gt
    (periodicHypercubicEvenBoundaryVacuumMoment_pos
      H N hN beta hbeta b)]

/-- Pointwise reciprocal-vacuum transport of a boundary Haar `L²` vector. -/
noncomputable def periodicHypercubicEvenBoundaryHaarToMarginalL2Function
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
    H N hN beta hbeta b * f b

/-- Reciprocal-vacuum transport is strongly measurable under the interacting
boundary marginal. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2Function_aestronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Function
        H N hN beta hbeta f)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta) := by
  apply AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous _ _)
  exact
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Weight_measurable
      H N hN beta hbeta).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)

/-- Reciprocal-vacuum transport belongs to the interacting boundary marginal
`L²`. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2Function_memLp
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    MemLp
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Function
        H N hN beta hbeta f)
      2
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H N hN beta hbeta) := by
  apply (memLp_two_iff_integrable_sq
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Function_aestronglyMeasurable
      H N hN beta hbeta f)).2
  rw [periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    H N hN beta hbeta]
  rw [integrable_withDensity_iff_integrable_smul
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H N hN beta hbeta)]
  have hf : Integrable (fun b => (f b) ^ 2)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
    (Lp.memLp f).integrable_sq
  apply hf.congr
  filter_upwards with b
  simp only [smul_eq_mul]
  change
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
      H N hN beta hbeta b : ℝ) *
      ((periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
        H N hN beta hbeta b * f b) ^ 2) =
      f b ^ 2
  rw [mul_pow]
  calc
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H N hN beta hbeta b : ℝ) *
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
        H N hN beta hbeta b ^ 2 * f b ^ 2) =
      ((periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H N hN beta hbeta b : ℝ) *
        periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
          H N hN beta hbeta b ^ 2) * f b ^ 2 := by ring
    _ = f b ^ 2 := by
      rw [periodicHypercubicEvenBoundaryMarginalDensityNNReal_mul_weight_sq]
      simp

end

end MathlibAnalytic
end MGAP4D
