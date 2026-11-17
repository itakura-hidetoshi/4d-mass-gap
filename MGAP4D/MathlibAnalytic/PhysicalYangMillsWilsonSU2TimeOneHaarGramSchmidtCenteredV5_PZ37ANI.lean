import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneOSBetaZeroExactKernelV5_PZ37ANH
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANI — exact SU(2) Wilson Gram--Schmidt Haar centering

ANH reduces the ORIGINAL full-periodic beta-zero OS boundary moment kernel
to the unchanged time-one observable's fiber open-half Haar mean.

Before any claim about its actual open-half fiber, one needs the concrete
input about the two theorem-generated SU(2) Wilson-energy modes.
The zeroth mode is exactly constant one (not an arbitrary normalized
abstract vector); hence the first higher mode has Haar expectation zero.
This uses the actual canonical normalized Haar L2 Gram--Schmidt,
orthonormality, and the chosen continuous representatives.

The next geometric problem remains the FIXED-boundary open-half time-one
marginal for H>0; the H=0 time-one slice is itself antipodal-fixed.
No identification of the original top-eigenspace-orthogonal physical
coefficients with the centered mode is claimed here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANI_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANI_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANI_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANI_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANI_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private def p4Q2PZ37ANI_haar : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- Explicitly expose the unchanged normalized original SU(2) Haar as a
probability. Definitional unfolding of the named local measure is not
reliable during later synthesis of finite-measure instances. -/
local instance p4Q2PZ37ANI_haarProbability :
    IsProbabilityMeasure p4Q2PZ37ANI_haar := by
  change IsProbabilityMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))
  infer_instance

local instance p4Q2PZ37ANI_haarFinite :
    IsFiniteMeasure p4Q2PZ37ANI_haar := by
  infer_instance

/-- The power-zero genuine Wilson-energy Haar L2 vector is EXACTLY the
constant-one normalized-Haar vector, with the original SU(2) measure. -/
theorem p4Q2PZ37ANI_originalWilsonEnergyPowerZero_eq_constOne :
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
        (by norm_num : 0 < (2 : ℕ)) 0 =
      Lp.const 2 p4Q2PZ37ANI_haar (1 : ℝ) := by
  let mu := p4Q2PZ37ANI_haar
  apply Lp.ext
  filter_upwards
    [specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn
      (by norm_num : 0 < (2 : ℕ)) 0,
     Lp.coeFn_const (μ := mu) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ))]
     with U hPower hOne
  calc
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
        (by norm_num : 0 < (2 : ℕ)) 0 U =
      specialUnitaryWilsonPlaquetteEnergyPower 2 0 U := hPower
    _ = 1 := by simp [specialUnitaryWilsonPlaquetteEnergyPower]
    _ = (Lp.const 2 mu (1 : ℝ)) U := by
      simpa only [Function.const_apply] using hOne.symm

/-- Canonical Gram--Schmidt starts from the actual Haar unit constant
since the degree-zero Wilson energy is identically one. -/
theorem p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 0 =
      Lp.const 2 p4Q2PZ37ANI_haar (1 : ℝ) := by
  let mu := p4Q2PZ37ANI_haar
  have hOneNorm : ‖Lp.const 2 mu (1 : ℝ)‖ = 1 := by
    simpa [measureReal_def] using
      (Lp.norm_const (μ := mu) (p := 2) (c := (1 : ℝ)) (by norm_num))
  change InnerProductSpace.gramSchmidtNormed ℝ
      (fun k : ℕ =>
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
          (by norm_num : 0 < (2 : ℕ)) k) 0 =
      Lp.const 2 mu (1 : ℝ)
  rw [InnerProductSpace.gramSchmidtNormed]
  have hFirst :
      InnerProductSpace.gramSchmidt ℝ
          (fun k : ℕ =>
            specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
              (by norm_num : 0 < (2 : ℕ)) k) 0 =
        specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
          (by norm_num : 0 < (2 : ℕ)) 0 := by
    simpa only using
      (InnerProductSpace.gramSchmidt_bot
        (𝕜 := ℝ)
        (f := fun k : ℕ =>
          specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
            (by norm_num : 0 < (2 : ℕ)) k))
  rw [hFirst, p4Q2PZ37ANI_originalWilsonEnergyPowerZero_eq_constOne]
  simp [hOneNorm]

/-- The exact SECOND normalized SU(2) Wilson-energy Gram--Schmidt L2
mode has zero Haar expectation, because it is orthogonal to the
ACTUAL constant first mode, not an abstract assumed constant. -/
theorem p4Q2PZ37ANI_originalWilsonHaarModeOne_integral_zero :
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 U
      ∂p4Q2PZ37ANI_haar) = 0 := by
  let mu := p4Q2PZ37ANI_haar
  have hOrtho :
      inner ℝ (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 0)
        (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1) = 0 :=
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal.inner_eq_zero
      (by decide : (0 : ℕ) ≠ 1)
  calc
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 U
      ∂p4Q2PZ37ANI_haar) =
      inner ℝ (Lp.const 2 mu (1 : ℝ))
        (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1) := by
        exact (realL2_inner_const_one_eq_integral _).symm
    _ = inner ℝ (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 0)
          (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1) := by
        simpa only [mu] using
          (congrArg
            (fun v : SpecialUnitaryNormalizedHaarL2 2 =>
              inner ℝ v (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1))
            (p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne).symm)
    _ = 0 := hOrtho

/-- The chosen continuous original Wilson mode is centered pointwise under
the ORIGINAL normalized SU(2) Haar law: not merely a formal L2 statement. -/
theorem p4Q2PZ37ANI_originalWilsonContinuousModeOne_haarMean_zero :
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 U
      ∂p4Q2PZ37ANI_haar) = 0 := by
  let mu := p4Q2PZ37ANI_haar
  let f : SpecialUnitaryNormalizedHaarL2 2 :=
    ContinuousMap.toLp
      (E := ℝ) 2 mu ℝ
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1)
  have hRep :
      f =ᵐ[mu] specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := mu)
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1)
  have hF :
      f = specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 := by
    exact specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp 1
  calc
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 U
      ∂p4Q2PZ37ANI_haar) =
        ∫ U, f U ∂mu := integral_congr_ae hRep.symm
    _ = ∫ U, specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 U
      ∂p4Q2PZ37ANI_haar := by rw [hF]
    _ = 0 := p4Q2PZ37ANI_originalWilsonHaarModeOne_integral_zero

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANI_originalWilsonEnergyPowerZero_eq_constOne
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANI_originalWilsonHaarModeOne_integral_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANI_originalWilsonContinuousModeOne_haarMean_zero
