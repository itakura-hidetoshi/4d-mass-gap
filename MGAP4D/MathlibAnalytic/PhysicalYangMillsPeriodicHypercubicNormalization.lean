import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactFactorizedEnvelope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteCardinality
import Mathlib.Data.ENNReal.Inv

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

/-- The extended-nonnegative plaquette multiplicity `6 * L_n^4`. -/
def plaquetteVolume
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (n : ℕ) : ENNReal :=
  ((6 * H.sideLength n ^ 4 : ℕ) : ENNReal)

/-- The canonical scale reciprocal to the number of periodic four-dimensional
plaquettes. -/
def reciprocalPlaquetteScale
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily) : ℕ → ENNReal :=
  fun n => (H.plaquetteVolume n)⁻¹

/-- The periodic four-dimensional plaquette volume is nonzero. -/
theorem plaquetteVolume_ne_zero
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (n : ℕ) :
    H.plaquetteVolume n ≠ 0 := by
  have hL : H.sideLength n ≠ 0 := Nat.ne_of_gt (H.sideLength_pos n)
  have hNat : 6 * H.sideLength n ^ 4 ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (pow_ne_zero 4 hL)
  exact_mod_cast hNat

/-- The periodic four-dimensional plaquette volume is finite. -/
theorem plaquetteVolume_ne_top
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (n : ℕ) :
    H.plaquetteVolume n ≠ ⊤ := by
  simp [plaquetteVolume]

/-- Reciprocal plaquette scaling cancels the exact four-dimensional plaquette
multiplicity. -/
theorem reciprocalPlaquetteScale_mul_volume
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (n : ℕ) :
    H.reciprocalPlaquetteScale n * H.plaquetteVolume n = 1 := by
  exact ENNReal.inv_mul_cancel
    (H.plaquetteVolume_ne_zero n) (H.plaquetteVolume_ne_top n)

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
      scale n * H.plaquetteVolume n ≤ bound

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

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

/-- Reciprocal plaquette scaling canonically supplies the scaled-volume receipt
with sharp bound one. -/
def reciprocalScaledVolumeBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    (H : E.PeriodicHypercubicPlaquetteFamily) :
    E.WilsonPeriodicHypercubicScaledVolumeBound
      H.reciprocalPlaquetteScale H :=
  { bound := 1
    bound_ne_top := by simp
    scaled_volume_le := by
      intro n
      exact le_of_eq (H.reciprocalPlaquetteScale_mul_volume n) }

/-- With reciprocal plaquette scaling, compact-energy and offset control together
with physical coercivity imply tightness; no separate volume normalization
estimate remains. -/
theorem isTight_of_reciprocalPlaquetteScale
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {offset : ℕ → ENNReal}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  H.reciprocalScaledVolumeBound.isTight M O D

/-- Reciprocal plaquette scaling reduces the periodic four-dimensional weak-limit
constructor to compact-energy control, offset control, and the physical
coercivity estimate. -/
noncomputable def weakLimit_of_reciprocalPlaquetteScale
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {offset : ℕ → ENNReal}
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  H.reciprocalScaledVolumeBound.toWeakLimit M O D

end ContinuousCompactGaugeWilsonPhysicalEmbedding.PeriodicHypercubicPlaquetteFamily

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

/-- Public constructor using the canonical reciprocal plaquette scale
`(6 * L_n^4)⁻¹`. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicReciprocalScale
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (offset : ℕ → ENNReal)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  H.weakLimit_of_reciprocalPlaquetteScale M O D

end

end MathlibAnalytic
end MGAP4D
