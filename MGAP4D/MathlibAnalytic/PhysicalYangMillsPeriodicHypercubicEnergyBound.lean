import MGAP4D.MathlibAnalytic.PhysicalYangMillsPeriodicHypercubicNormalization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonEnergyUniformization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- The zero affine offset has a uniform finite bound. -/
def zeroWilsonOffsetUniformBound :
    WilsonOffsetUniformBound (fun _ : ℕ => (0 : ENNReal)) :=
  { bound := 0
    bound_ne_top := by simp
    offset_le := by simp }

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- Reciprocal plaquette scaling and a uniform pointwise plaquette-energy bound imply tightness with zero offset. -/
theorem isTight_of_reciprocalPlaquetteScale_zeroOffset
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  H.isTight_of_reciprocalPlaquetteScale
    B.toWilsonCompactEnergyMaximumUniformBound
    zeroWilsonOffsetUniformBound D

/-- Reciprocal plaquette scaling, a uniform pointwise energy bound, and zero offset produce a physical weak limit. -/
noncomputable def weakLimit_of_reciprocalPlaquetteScale_zeroOffset
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  H.weakLimit_of_reciprocalPlaquetteScale
    B.toWilsonCompactEnergyMaximumUniformBound
    zeroWilsonOffsetUniformBound D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- Public constructor requiring only periodic geometry, a uniform pointwise plaquette-energy bound, and zero-offset coercivity. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicEnergyBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  H.weakLimit_of_reciprocalPlaquetteScale_zeroOffset B D

/-- A real pointwise energy estimate is enough to invoke the periodic reciprocal-scale weak-limit constructor. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicRealEnergyBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (energyBound : ℝ)
    (pointwise_le : ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g ≤ energyBound)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicEnergyBound
    E Phi H (E.wilsonPlaquetteEnergyUniformBound_of_real energyBound pointwise_le) D

end

end MathlibAnalytic
end MGAP4D
