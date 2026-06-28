import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryTraceEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A Wilson scaling family whose gauge group at every scale is identified with
one fixed special-unitary matrix group and whose plaquette energy is the standard
normalized real-trace Wilson energy under that identification. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryGaugeFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  rank : ℕ
  rank_pos : 0 < rank
  gaugeEquiv :
    ∀ n,
      (E.system n).base.Gauge ≃*
        Matrix.specialUnitaryGroup (Fin rank) ℂ
  plaquetteEnergy_eq :
    ∀ n (g : (E.system n).base.Gauge),
      (E.system n).base.plaquetteEnergy g =
        1 - normalizedSpecialUnitaryRealTrace rank (gaugeEquiv n g)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryGaugeFamily

/-- A scale-wise gauge-group equivalence supplies the corresponding
special-unitary representation receipt. -/
def toWilsonSpecialUnitaryTraceEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (G : E.WilsonSpecialUnitaryGaugeFamily) :
    E.WilsonSpecialUnitaryTraceEnergyFamily :=
  { rank := G.rank
    rank_pos := G.rank_pos
    representation := fun n => (G.gaugeEquiv n).toMonoidHom
    plaquetteEnergy_eq := G.plaquetteEnergy_eq }

/-- A scale-wise special-unitary gauge identification supplies the unitary trace
energy receipt. -/
def toWilsonUnitaryTraceEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (G : E.WilsonSpecialUnitaryGaugeFamily) :
    E.WilsonUnitaryTraceEnergyFamily :=
  G.toWilsonSpecialUnitaryTraceEnergyFamily.toWilsonUnitaryTraceEnergyFamily

/-- A scale-wise special-unitary gauge identification supplies the normalized
character receipt. -/
def toWilsonNormalizedCharacterEnergyFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (G : E.WilsonSpecialUnitaryGaugeFamily) :
    E.WilsonNormalizedCharacterEnergyFamily :=
  G.toWilsonSpecialUnitaryTraceEnergyFamily.toWilsonNormalizedCharacterEnergyFamily

/-- Standard Wilson plaquette energies on the identified `SU(N)` gauge groups
are bounded above by two. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (G : E.WilsonSpecialUnitaryGaugeFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 :=
  G.toWilsonSpecialUnitaryTraceEnergyFamily.plaquetteEnergy_le_two n g

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryGaugeFamily

/-- Exact periodic geometry, scale-wise identification with one fixed `SU(N)`
gauge group, and one proper `NNReal` physical functional controlled by the
reciprocal-volume action produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryGaugeProperNNRealFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (G : E.WilsonSpecialUnitaryGaugeFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryTraceProperNNRealFunctional
    E H G.toWilsonSpecialUnitaryTraceEnergyFamily
      functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
