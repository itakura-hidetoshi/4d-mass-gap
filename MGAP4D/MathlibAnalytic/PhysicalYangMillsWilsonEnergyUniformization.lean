import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactFactorizedEnvelope

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteEnergyUniformBound

/-- A uniform pointwise plaquette-energy bound also bounds every compactness-generated maximum. -/
def toWilsonCompactEnergyMaximumUniformBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (B : E.WilsonPlaquetteEnergyUniformBound) :
    E.WilsonCompactEnergyMaximumUniformBound :=
  { bound := B.energyBound
    bound_ne_top := B.energyBound_ne_top
    maximum_le := by
      intro n
      change E.plaquetteEnergyObservable n
          (E.system n).plaquetteEnergyMaximizer ≤ B.energyBound
      exact B.pointwise_le n (E.system n).plaquetteEnergyMaximizer }

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPlaquetteEnergyUniformBound

/-- A real uniform upper bound for the original plaquette energies gives a finite extended-real receipt. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.wilsonPlaquetteEnergyUniformBound_of_real
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (energyBound : ℝ)
    (pointwise_le : ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g ≤ energyBound) :
    E.WilsonPlaquetteEnergyUniformBound :=
  { energyBound := ENNReal.ofReal energyBound
    energyBound_ne_top := ENNReal.ofReal_ne_top
    pointwise_le := by
      intro n g
      exact ENNReal.ofReal_le_ofReal (pointwise_le n g) }

/-- A real pointwise energy bound also controls the compact maxima uniformly. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.wilsonCompactEnergyMaximumUniformBound_of_real
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (energyBound : ℝ)
    (pointwise_le : ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g ≤ energyBound) :
    E.WilsonCompactEnergyMaximumUniformBound :=
  (E.wilsonPlaquetteEnergyUniformBound_of_real energyBound pointwise_le).toWilsonCompactEnergyMaximumUniformBound

end

end MathlibAnalytic
end MGAP4D
