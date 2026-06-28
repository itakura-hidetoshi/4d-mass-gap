import MGAP4D.MathlibAnalytic.PhysicalYangMillsPeriodicHypercubicEnergyBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A standard normalized-character presentation of the Wilson plaquette energy.
The normalized real character lies in `[-1,1]`, and the energy is `1 - character`. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonNormalizedCharacterEnergyFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  normalizedCharacter :
    ∀ n, (E.system n).base.Gauge → ℝ
  normalizedCharacter_mem_Icc :
    ∀ n (g : (E.system n).base.Gauge),
      normalizedCharacter n g ∈ Set.Icc (-1 : ℝ) 1
  plaquetteEnergy_eq :
    ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g =
        1 - normalizedCharacter n g

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonNormalizedCharacterEnergyFamily

/-- Standard normalized-character Wilson plaquette energies are bounded above by two. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 := by
  rw [W.plaquetteEnergy_eq n g]
  linarith [(W.normalizedCharacter_mem_Icc n g).1]

/-- The normalized-character presentation supplies the sharp universal energy bound `2`. -/
def toWilsonPlaquetteEnergyUniformBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonNormalizedCharacterEnergyFamily) :
    E.WilsonPlaquetteEnergyUniformBound :=
  E.wilsonPlaquetteEnergyUniformBound_of_real 2
    (fun n g => W.plaquetteEnergy_le_two n g)

/-- The compactness-generated plaquette-energy maxima are uniformly bounded by `2`. -/
def toWilsonCompactEnergyMaximumUniformBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (W : E.WilsonNormalizedCharacterEnergyFamily) :
    E.WilsonCompactEnergyMaximumUniformBound :=
  W.toWilsonPlaquetteEnergyUniformBound.toWilsonCompactEnergyMaximumUniformBound

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonNormalizedCharacterEnergyFamily

/-- Periodic four-dimensional geometry, standard normalized-character Wilson energy,
and a zero-offset coercive estimate produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicNormalizedCharacter
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicEnergyBound
    E Phi H W.toWilsonPlaquetteEnergyUniformBound D

end

end MathlibAnalytic
end MGAP4D
