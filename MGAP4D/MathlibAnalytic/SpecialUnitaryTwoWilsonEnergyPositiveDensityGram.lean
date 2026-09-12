import MGAP4D.MathlibAnalytic.ContinuousInfiniteRangePowerWithDensityGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance su2PositiveDensityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2PositiveDensityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2PositiveDensitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2PositiveDensityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2PositiveDensityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2PositiveDensityHaarMeasure :
    Measure.IsHaarMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The concrete `SU(2)` Wilson-energy power family remains linearly
independent after tilting normalized Haar measure by any finite density that is
nonzero almost everywhere.

This is the exact weighted-Haar form required before substituting a positive
Wilson Boltzmann density. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoPower_withDensity_toLp_linearIndependent
    (w : Matrix.specialUnitaryGroup (Fin 2) ℂ → ENNReal)
    (hw : AEMeasurable w
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (hw_ne_zero : ∀ᵐ U ∂
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      w U ≠ 0)
    [IsFiniteMeasure
      ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity w)] :
    LinearIndependent ℝ
      (fun k : ℕ =>
        ContinuousMap.toLp
          (E := ℝ) 2
          ((normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity w) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ k)) := by
  exact continuousMap_infiniteRange_powerFamily_toLp_withDensity_linearIndependent
    w hw hw_ne_zero
    specialUnitaryWilsonPlaquetteEnergyTwoContinuous
    specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange

/-- Hence every finite initial `SU(2)` Wilson-energy power family has nonzero
weighted-Haar `L²` Gram determinant under any finite density that is nonzero
almost everywhere. -/
theorem specialUnitaryWilsonPlaquetteEnergyTwoPower_withDensity_fin_gram_det_ne_zero
    (w : Matrix.specialUnitaryGroup (Fin 2) ℂ → ENNReal)
    (hw : AEMeasurable w
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (hw_ne_zero : ∀ᵐ U ∂
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      w U ≠ 0)
    [IsFiniteMeasure
      ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity w)]
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          ((normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin 2) ℂ)).withDensity w) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuous ^ (j : ℕ)))).det ≠ 0 := by
  exact
    continuousMap_infiniteRange_powerFamily_toLp_withDensity_fin_gram_det_ne_zero
      w hw hw_ne_zero
      specialUnitaryWilsonPlaquetteEnergyTwoContinuous
      specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange k

end

end MathlibAnalytic
end MGAP4D
