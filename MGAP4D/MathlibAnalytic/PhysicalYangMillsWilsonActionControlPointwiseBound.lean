import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionPointwiseBound

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A finite uniform pointwise bound for the affine-renormalized Wilson action
control observable itself. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  pointwise_le :
    ∀ n U,
      E.renormalizedWilsonActionObservable scale offset n U ≤ bound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound

/-- Probability normalization turns a pointwise control bound into the
corresponding uniform control-moment receipt. -/
def toWilsonActionControlMomentBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset) :
    E.WilsonActionControlMomentBound scale offset :=
  { momentBound := B.bound
    momentBound_ne_top := B.bound_ne_top
    uniform_lintegral_le := by
      intro n
      letI : IsProbabilityMeasure (E.system n).gibbsMeasure :=
        continuous_compact_gauge_gibbsMeasure_isProbabilityMeasure (E.system n)
      calc
        ∫⁻ U,
            E.renormalizedWilsonActionObservable scale offset n U
            ∂((E.system n).gibbsProbabilityMeasure :
              Measure (E.system n).base.Configuration) ≤
            ∫⁻ _U, B.bound
              ∂((E.system n).gibbsProbabilityMeasure :
                Measure (E.system n).base.Configuration) :=
          lintegral_mono (B.pointwise_le n)
        _ = B.bound := by simp }

/-- A pointwise renormalized-action bound plus deterministic physical
coercivity implies tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  D.isTight B.toWilsonActionControlMomentBound

/-- A pointwise renormalized-action bound produces the physical weak limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (B : E.WilsonActionControlUniformPointwiseBound scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit B.toWilsonActionControlMomentBound

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlUniformPointwiseBound

/-- Uniform raw-action and affine-coefficient bounds imply a uniform pointwise
bound for the affine-renormalized action. -/
def WilsonActionAffineCoefficientBounds.toWilsonActionControlUniformPointwiseBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (B : E.WilsonActionUniformPointwiseBound) :
    E.WilsonActionControlUniformPointwiseBound scale offset :=
  { bound := C.scaleBound * B.bound + C.offsetBound
    bound_ne_top :=
      ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top C.scaleBound_ne_top B.bound_ne_top,
          C.offsetBound_ne_top⟩
    pointwise_le := by
      intro n U
      rw [E.renormalizedWilsonActionObservable_eq]
      gcongr
      · exact C.scale_le n
      · exact B.pointwise_le n U
      · exact C.offset_le n }

end

end MathlibAnalytic
end MGAP4D
