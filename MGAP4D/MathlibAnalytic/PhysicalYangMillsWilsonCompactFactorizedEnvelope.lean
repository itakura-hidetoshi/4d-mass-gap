import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactCardinalityEnvelope

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- A uniform bound for the product of the renormalization scale and the number
of plaquettes. This isolates the geometric finite-volume growth from the
plaquette-energy estimate. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonScaledPlaquetteCardinalityBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  scaled_cardinality_le :
    ∀ n,
      scale n *
          ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) ≤
        bound

/-- A finite uniform bound for the compactness-generated plaquette-energy
maxima along the lattice family. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonCompactEnergyMaximumUniformBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  maximum_le : ∀ n, E.compactPlaquetteEnergyMaximum n ≤ bound

/-- A finite uniform bound for the affine offsets. -/
structure WilsonOffsetUniformBound (offset : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  offset_le : ∀ n, offset n ≤ bound

/-- The geometric cardinality estimate, the compact-energy estimate, and the
offset estimate combine into the explicit compact plaquette-cardinality
envelope. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.compactPlaquetteCardinalityEnvelope_of_factorizedBounds
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (C : E.WilsonScaledPlaquetteCardinalityBound scale)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset) :
    E.WilsonCompactPlaquetteCardinalityEnvelope scale offset :=
  { bound := C.bound * M.bound + O.bound
    bound_ne_top :=
      ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top C.bound_ne_top M.bound_ne_top,
          O.bound_ne_top⟩
    envelope_le := by
      intro n
      calc
        scale n *
              (((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal) *
                E.compactPlaquetteEnergyMaximum n) +
            offset n =
            (scale n *
                ((Fintype.card (E.system n).base.Plaquette : ℕ) : ENNReal)) *
              E.compactPlaquetteEnergyMaximum n +
            offset n := by
              rw [mul_assoc]
        _ ≤ C.bound * M.bound + O.bound := by
          gcongr
          · exact C.scaled_cardinality_le n
          · exact M.maximum_le n
          · exact O.offset_le n }

/-- Factorized geometric, energy, and offset bounds together with physical
coercivity imply tightness. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.isTight_of_compactPlaquetteFactorizedBounds
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (C : E.WilsonScaledPlaquetteCardinalityBound scale)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  (E.compactPlaquetteCardinalityEnvelope_of_factorizedBounds C M O).isTight D

/-- Public weak-limit constructor from separate geometric growth, compact-energy,
offset, and physical coercivity receipts. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteFactorizedBounds
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (C : E.WilsonScaledPlaquetteCardinalityBound scale)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (E.compactPlaquetteCardinalityEnvelope_of_factorizedBounds C M O).toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
