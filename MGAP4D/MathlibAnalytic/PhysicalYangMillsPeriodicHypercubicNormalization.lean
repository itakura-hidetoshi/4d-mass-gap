import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactFactorizedEnvelope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteCardinality

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Identification of every plaquette type in a Wilson scaling family with the
positively based plaquettes of a periodic four-dimensional hypercubic box. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  sideLength : ℕ → ℕ
  sideLength_pos : ∀ n, 0 < sideLength n
  plaquetteEquiv :
    ∀ n,
      (E.system n).base.Plaquette ≃
        PeriodicHypercubicPlaquette (sideLength n)

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- The plaquette cardinality of an identified periodic four-dimensional box is
exactly `6 * sideLength^4`. -/
theorem plaquette_card_eq
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (n : ℕ) :
    Fintype.card (E.system n).base.Plaquette =
      6 * H.sideLength n ^ 4 := by
  letI : NeZero (H.sideLength n) :=
    ⟨Nat.ne_of_gt (H.sideLength_pos n)⟩
  calc
    Fintype.card (E.system n).base.Plaquette =
        Fintype.card (PeriodicHypercubicPlaquette (H.sideLength n)) :=
      Fintype.card_congr (H.plaquetteEquiv n)
    _ = 6 * H.sideLength n ^ 4 :=
      periodicHypercubicPlaquette_card (H.sideLength n)

end ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- A finite bound for the renormalization scale multiplied by the explicit
four-dimensional plaquette volume `6 * L_n^4`. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPeriodicHypercubicScaledVolumeBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale : ℕ → ENNReal)
    (H : E.PeriodicHypercubicPlaquetteFamily) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  scaled_volume_le :
    ∀ n,
      scale n * (((6 * H.sideLength n ^ 4 : ℕ) : ENNReal)) ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPeriodicHypercubicScaledVolumeBound

/-- The explicit four-dimensional volume bound supplies the abstract scaled
plaquette-cardinality receipt. -/
def toWilsonScaledPlaquetteCardinalityBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale : ℕ → ENNReal}
    {H : E.PeriodicHypercubicPlaquetteFamily}
    (V : E.WilsonPeriodicHypercubicScaledVolumeBound scale H) :
    E.WilsonScaledPlaquetteCardinalityBound scale :=
  { bound := V.bound
    bound_ne_top := V.bound_ne_top
    scaled_cardinality_le := by
      intro n
      rw [H.plaquette_card_eq n]
      exact V.scaled_volume_le n }

/-- Explicit four-dimensional volume growth, compact-energy control, offset
control, and physical coercivity imply tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    {H : E.PeriodicHypercubicPlaquetteFamily}
    (V : E.WilsonPeriodicHypercubicScaledVolumeBound scale H)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  E.isTight_of_compactPlaquetteFactorizedBounds
    V.toWilsonScaledPlaquetteCardinalityBound M O D

/-- Explicit four-dimensional periodic volume growth and the remaining analytic
receipts produce a physical continuum weak limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    {H : E.PeriodicHypercubicPlaquetteFamily}
    (V : E.WilsonPeriodicHypercubicScaledVolumeBound scale H)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteFactorizedBounds
    E Phi scale offset V.toWilsonScaledPlaquetteCardinalityBound M O D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonPeriodicHypercubicScaledVolumeBound

/-- Public constructor with the four-dimensional periodic plaquette multiplicity
made explicit as `6 * L_n^4`. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicBounds
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (V : E.WilsonPeriodicHypercubicScaledVolumeBound scale H)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  V.toWeakLimit M O D

end

end MathlibAnalytic
end MGAP4D
