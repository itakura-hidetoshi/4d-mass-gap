import MGAP4D.MathlibAnalytic.ContinuousInfiniteRangePowerLpLinearIndependent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyPowerHaarModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Order.Interval.Set.Infinite

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set

noncomputable section

/-- The standard real rotation matrix, regarded as a complex `2 × 2` matrix. -/
def specialUnitaryTwoRotationMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), -(Real.sin t : ℂ);
     (Real.sin t : ℂ), (Real.cos t : ℂ)]

/-- The real rotation matrix is unitary after scalar extension to `ℂ`. -/
theorem specialUnitaryTwoRotationMatrix_mem_unitaryGroup (t : ℝ) :
    specialUnitaryTwoRotationMatrix t ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
  have hc : Complex.cos (t : ℂ) = (Real.cos t : ℂ) :=
    (Complex.ofReal_cos t).symm
  have hs : Complex.sin (t : ℂ) = (Real.sin t : ℂ) :=
    (Complex.ofReal_sin t).symm
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specialUnitaryTwoRotationMatrix, Matrix.mul_apply, hc, hs] <;>
    ring_nf <;>
    norm_num [← Complex.ofReal_mul, ← Complex.ofReal_add,
      Real.sin_sq_add_cos_sq]

/-- The real rotation matrix has determinant one. -/
theorem specialUnitaryTwoRotationMatrix_det (t : ℝ) :
    Matrix.det (specialUnitaryTwoRotationMatrix t) = 1 := by
  have hc : Complex.cos (t : ℂ) = (Real.cos t : ℂ) :=
    (Complex.ofReal_cos t).symm
  have hs : Complex.sin (t : ℂ) = (Real.sin t : ℂ) :=
    (Complex.ofReal_sin t).symm
  simp [specialUnitaryTwoRotationMatrix, Matrix.det_fin_two, hc, hs]
  norm_num [← Complex.ofReal_mul, ← Complex.ofReal_add,
    Real.sin_sq_add_cos_sq]

/-- The explicit one-parameter rotation subgroup, packaged as an element of
`SU(2)`. -/
def specialUnitaryTwoRotation (t : ℝ) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨specialUnitaryTwoRotationMatrix t,
    specialUnitaryTwoRotationMatrix_mem_unitaryGroup t,
    specialUnitaryTwoRotationMatrix_det t⟩

/-- Its trace is exactly `2 cos t`. -/
theorem specialUnitaryTwoRotation_trace (t : ℝ) :
    Matrix.trace
        ((specialUnitaryTwoRotation t :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (2 * Real.cos t : ℝ) := by
  simp [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix,
    Matrix.trace_fin_two]
  ring

/-- Along the rotation subgroup, the standard normalized Wilson plaquette
energy is exactly `1 - cos t`. -/
theorem specialUnitaryWilsonPlaquetteEnergy_two_rotation (t : ℝ) :
    specialUnitaryWilsonPlaquetteEnergy 2 (specialUnitaryTwoRotation t) =
      1 - Real.cos t := by
  unfold specialUnitaryWilsonPlaquetteEnergy
  rw [specialUnitaryTwoRotation_trace]
  norm_num [Complex.cos_ofReal_re]

/-- Every value in `[0,2]` is attained by the `SU(2)` Wilson plaquette energy.
The witness is the rotation with angle `arccos (1-y)`. -/
theorem Icc_zero_two_subset_range_specialUnitaryWilsonPlaquetteEnergy_two :
    Set.Icc (0 : ℝ) 2 ⊆
      Set.range (specialUnitaryWilsonPlaquetteEnergy 2) := by
  intro y hy
  have hx : 1 - y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  refine ⟨specialUnitaryTwoRotation (Real.arccos (1 - y)), ?_⟩
  rw [specialUnitaryWilsonPlaquetteEnergy_two_rotation,
    Real.cos_arccos hx.1 hx.2]
  ring

/-- Consequently, the `SU(2)` Wilson plaquette energy has infinite range. -/
theorem specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange :
    (Set.range (specialUnitaryWilsonPlaquetteEnergy 2)).Infinite :=
  (Set.Icc_infinite (show (0 : ℝ) < 2 by norm_num)).mono
    Icc_zero_two_subset_range_specialUnitaryWilsonPlaquetteEnergy_two

local instance specialUnitaryTwoWilsonEnergyTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoWilsonEnergyCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoWilsonEnergySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoWilsonEnergyMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoWilsonEnergyBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoWilsonEnergyHaarMeasure :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The standard `SU(2)` Wilson energy as an actual real continuous function. -/
noncomputable def specialUnitaryWilsonPlaquetteEnergyTwoContinuous :
    C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) :=
  ⟨specialUnitaryWilsonPlaquetteEnergy 2,
    continuous_specialUnitaryWilsonPlaquetteEnergy 2⟩

/-- The concrete Wilson-energy power family is linearly independent in
normalized-Haar real `L²(SU(2))`.

This is the model-specific specialization of the generic infinite-range
continuous-power theorem. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoPower_toLp_linearIndependent :
    LinearIndependent ℝ
      (fun k : ℕ =>
        ContinuousMap.toLp
          (E := ℝ) 2
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k)) := by
  exact continuousMap_infiniteRange_powerFamily_toLp_linearIndependent
    specialUnitaryWilsonPlaquetteEnergyTwoContinuous
    specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange

end

end MathlibAnalytic
end MGAP4D
