import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableSupremum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionControl

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlFiniteSupremum
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  supremum_ne_top :
    (⨆ n,
      ∫⁻ U,
        E.renormalizedWilsonActionObservable scale offset n U
        ∂((E.system n).gibbsProbabilityMeasure :
          Measure (E.system n).base.Configuration)) ≠ ⊤

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlFiniteSupremum

def toWilsonActionControlMomentBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (S : E.WilsonActionControlFiniteSupremum scale offset) :
    E.WilsonActionControlMomentBound scale offset :=
  { momentBound :=
      ⨆ n,
        ∫⁻ U,
          E.renormalizedWilsonActionObservable scale offset n U
          ∂((E.system n).gibbsProbabilityMeasure :
            Measure (E.system n).base.Configuration)
    momentBound_ne_top := S.supremum_ne_top
    uniform_lintegral_le := fun n =>
      le_iSup
        (fun k =>
          ∫⁻ U,
            E.renormalizedWilsonActionObservable scale offset k U
            ∂((E.system k).gibbsProbabilityMeasure :
              Measure (E.system k).base.Configuration)) n }

theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (S : E.WilsonActionControlFiniteSupremum scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  D.isTight S.toWilsonActionControlMomentBound

noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (S : E.WilsonActionControlFiniteSupremum scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit S.toWilsonActionControlMomentBound

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlFiniteSupremum

noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_actionExpectationSupremum
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (S : E.WilsonActionControlFiniteSupremum scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  S.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
