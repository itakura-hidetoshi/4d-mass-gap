import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyPositiveDensityGram

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance su2ExponentialDensityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ExponentialDensityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ExponentialDensitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ExponentialDensityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ExponentialDensityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ExponentialDensityHaarMeasure :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The concrete single-plaquette Wilson exponential density on normalized
Haar `SU(2)`.

It is deliberately left unnormalized: multiplying a measure by a positive
scalar cannot affect the finite power-family nondegeneracy proved below, and
this form is exactly the local Boltzmann factor `exp (-beta * E_W)`. -/
noncomputable def specialUnitaryTwoWilsonEnergyExponentialDensity
    (beta : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ENNReal :=
  ENNReal.ofReal
    (Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 U))

/-- The concrete Wilson exponential density is measurable. -/
theorem specialUnitaryTwoWilsonEnergyExponentialDensity_measurable
    (beta : ℝ) :
    Measurable (specialUnitaryTwoWilsonEnergyExponentialDensity beta) := by
  unfold specialUnitaryTwoWilsonEnergyExponentialDensity
  fun_prop

/-- The concrete Wilson exponential density is everywhere nonzero. -/
theorem specialUnitaryTwoWilsonEnergyExponentialDensity_ne_zero
    (beta : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoWilsonEnergyExponentialDensity beta U ≠ 0 := by
  unfold specialUnitaryTwoWilsonEnergyExponentialDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

/-- At nonnegative coupling the unnormalized Wilson density is bounded by one.
This is exactly where nonnegativity of the Wilson plaquette energy enters. -/
theorem specialUnitaryTwoWilsonEnergyExponentialDensity_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoWilsonEnergyExponentialDensity beta U ≤ 1 := by
  unfold specialUnitaryTwoWilsonEnergyExponentialDensity
  rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hbeta)
    (specialUnitaryWilsonPlaquetteEnergy_nonneg 2 U)

/-- The Wilson exponential tilt of normalized Haar `SU(2)` is finite for every
nonnegative coupling.  The proof uses only the pointwise bound by one and the
fact that normalized Haar is a probability measure. -/
theorem specialUnitaryTwoWilsonEnergyExponentialDensity_lintegral_ne_top
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ U,
      specialUnitaryTwoWilsonEnergyExponentialDensity beta U
      ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))) ≠ ⊤ := by
  have hle :
      (∫⁻ U,
        specialUnitaryTwoWilsonEnergyExponentialDensity beta U
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))) ≤ 1 := by
    calc
      (∫⁻ U,
        specialUnitaryTwoWilsonEnergyExponentialDensity beta U
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))) ≤
          ∫⁻ _ : Matrix.specialUnitaryGroup (Fin 2) ℂ, (1 : ENNReal)
            ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
              apply lintegral_mono
              intro U
              exact specialUnitaryTwoWilsonEnergyExponentialDensity_le_one
                beta hbeta U
      _ = 1 := by simp
  exact ne_top_of_le_ne_top (by simp) hle

/-- The concrete Wilson exponential density therefore generates a finite
weighted Haar measure without adding any new model assumption. -/
theorem specialUnitaryTwoWilsonEnergyExponentialDensity_isFiniteMeasure
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity
        (specialUnitaryTwoWilsonEnergyExponentialDensity beta)) := by
  exact isFiniteMeasure_withDensity
    (specialUnitaryTwoWilsonEnergyExponentialDensity_lintegral_ne_top beta hbeta)

/-- At every nonnegative coupling, all `SU(2)` Wilson-energy powers remain
linearly independent in `L²` of the concrete Wilson-exponentially tilted Haar
measure. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoPower_exponentialDensity_toLp_linearIndependent
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    LinearIndependent ℝ
      (fun k : ℕ =>
        ContinuousMap.toLp
          (E := ℝ) 2
          ((normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity
              (specialUnitaryTwoWilsonEnergyExponentialDensity beta)) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k)) := by
  letI : IsFiniteMeasure
      ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity
        (specialUnitaryTwoWilsonEnergyExponentialDensity beta)) :=
    specialUnitaryTwoWilsonEnergyExponentialDensity_isFiniteMeasure beta hbeta
  exact
    specialUnitaryWilsonPlaquetteEnergyTwoPower_withDensity_toLp_linearIndependent
      (specialUnitaryTwoWilsonEnergyExponentialDensity beta)
      (specialUnitaryTwoWilsonEnergyExponentialDensity_measurable beta).aemeasurable
      (Filter.Eventually.of_forall
        (specialUnitaryTwoWilsonEnergyExponentialDensity_ne_zero beta))

/-- Consequently every finite initial Wilson-energy power family has nonzero
Gram determinant for the concrete nonnegative-coupling Wilson exponential
density. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoPower_exponentialDensity_fin_gram_det_ne_zero
    (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          ((normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity
              (specialUnitaryTwoWilsonEnergyExponentialDensity beta)) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ (j : ℕ)))).det ≠ 0 := by
  letI : IsFiniteMeasure
      ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity
        (specialUnitaryTwoWilsonEnergyExponentialDensity beta)) :=
    specialUnitaryTwoWilsonEnergyExponentialDensity_isFiniteMeasure beta hbeta
  exact
    specialUnitaryWilsonPlaquetteEnergyTwoPower_withDensity_fin_gram_det_ne_zero
      (specialUnitaryTwoWilsonEnergyExponentialDensity beta)
      (specialUnitaryTwoWilsonEnergyExponentialDensity_measurable beta).aemeasurable
      (Filter.Eventually.of_forall
        (specialUnitaryTwoWilsonEnergyExponentialDensity_ne_zero beta))
      k

end

end MathlibAnalytic
end MGAP4D
