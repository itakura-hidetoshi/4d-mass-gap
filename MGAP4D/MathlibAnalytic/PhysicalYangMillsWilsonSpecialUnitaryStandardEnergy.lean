import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A Wilson scaling family stated directly using the canonical continuous
`SU(N)` plaquette-energy function. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryStandardEnergyFamily
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
        specialUnitaryWilsonPlaquetteEnergy rank (gaugeEquiv n g)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryStandardEnergyFamily

/-- The canonical `SU(N)` plaquette-energy receipt supplies the conventional
matrix-trace formula receipt. -/
def toWilsonSpecialUnitaryMatrixTraceFormulaFamily
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (S : E.WilsonSpecialUnitaryStandardEnergyFamily) :
    E.WilsonSpecialUnitaryMatrixTraceFormulaFamily :=
  { rank := S.rank
    rank_pos := S.rank_pos
    gaugeEquiv := S.gaugeEquiv
    plaquetteEnergy_eq := by
      intro n g
      rw [S.plaquetteEnergy_eq n g]
      rfl }

/-- Canonical `SU(N)` Wilson plaquette energies are uniformly bounded by two. -/
theorem plaquetteEnergy_le_two
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (S : E.WilsonSpecialUnitaryStandardEnergyFamily)
    (n : ℕ)
    (g : (E.system n).base.Gauge) :
    (E.system n).base.plaquetteEnergy g ≤ 2 :=
  S.toWilsonSpecialUnitaryMatrixTraceFormulaFamily.plaquetteEnergy_le_two n g

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonSpecialUnitaryStandardEnergyFamily

/-- Exact periodic geometry, the canonical continuous `SU(N)` Wilson energy,
and one proper `NNReal` physical functional controlled by the reciprocal-volume
action produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryStandardEnergyProperNNRealFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (S : E.WilsonSpecialUnitaryStandardEnergyFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryMatrixTraceProperNNRealFunctional
    E H S.toWilsonSpecialUnitaryMatrixTraceFormulaFamily
      functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
