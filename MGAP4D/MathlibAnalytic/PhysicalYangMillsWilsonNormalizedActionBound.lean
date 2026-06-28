import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonNormalizedCharacterEnergy

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- For normalized-character Wilson energy and reciprocal plaquette scaling, the
explicit compact plaquette-cardinality envelope has the sharp bound `2`. -/
def normalizedCharacterReciprocalCardinalityEnvelope
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily) :
    E.WilsonCompactPlaquetteCardinalityEnvelope
      H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal)) :=
  { bound := 2
    bound_ne_top := by simp
    envelope_le := by
      intro n
      have hCard :
          H.reciprocalPlaquetteScale n *
              ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) ≤ 1 :=
        H.reciprocalScaledVolumeBound.toWilsonScaledPlaquetteCardinalityBound.scaled_cardinality_le n
      have hMaximum : E.compactPlaquetteEnergyMaximum n ≤ (2 : ENNReal) := by
        change ENNReal.ofReal
            ((E.system n).base.plaquetteEnergy
              (E.system n).plaquetteEnergyMaximizer) ≤ (2 : ENNReal)
        simpa using ENNReal.ofReal_le_ofReal
          (W.plaquetteEnergy_le_two n (E.system n).plaquetteEnergyMaximizer)
      simp only [Pi.zero_apply, add_zero]
      calc
        H.reciprocalPlaquetteScale n *
              (((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) *
                E.compactPlaquetteEnergyMaximum n) =
            (H.reciprocalPlaquetteScale n *
                ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal)) *
              E.compactPlaquetteEnergyMaximum n := by
                rw [mul_assoc]
        _ ≤ 1 * 2 := by
          gcongr
        _ = 2 := by norm_num }

/-- The reciprocal-volume normalized Wilson action is uniformly bounded by `2`
for every lattice scale and every configuration. -/
def normalizedCharacterActionUniformPointwiseBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily) :
    E.WilsonActionControlUniformPointwiseBound
      H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal)) :=
  (H.normalizedCharacterReciprocalCardinalityEnvelope W).toWilsonCompactPlaquetteNormalizationEnvelope.toWilsonActionControlUniformPointwiseBound

/-- Explicit sharp pointwise estimate for the reciprocal-volume normalized
Wilson action. -/
theorem renormalizedWilsonActionObservable_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (n : ℕ)
    (U : (E.system n).base.Configuration) :
    E.renormalizedWilsonActionObservable
        H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal)) n U ≤ 2 :=
  (H.normalizedCharacterActionUniformPointwiseBound W).pointwise_le n U

/-- The sharp normalized-action bound and a coercive interpolation estimate imply tightness. -/
theorem isTight_of_normalizedCharacterAction
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  (H.normalizedCharacterActionUniformPointwiseBound W).isTight D

/-- The sharp normalized-action bound and a coercive interpolation estimate
produce a physical continuum weak limit. -/
noncomputable def weakLimit_of_normalizedCharacterAction
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (H.normalizedCharacterActionUniformPointwiseBound W).toWeakLimit D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- Public weak-limit constructor from exact periodic geometry, normalized-character
Wilson energy, and the remaining physical coercive interpolation estimate. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_normalizedCharacterActionBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  H.weakLimit_of_normalizedCharacterAction W D

end

end MathlibAnalytic
end MGAP4D
