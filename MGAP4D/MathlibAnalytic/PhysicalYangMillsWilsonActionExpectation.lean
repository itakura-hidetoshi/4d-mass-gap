import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionControl
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The nonnegative extended-real version of the finite Wilson action. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.wilsonActionObservable
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ)
    (U : (E.system n).base.Configuration) : ENNReal :=
  ENNReal.ofReal ((E.system n).base.wilsonAction U)

@[simp]
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.renormalizedWilsonActionObservable_eq
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal)
    (n : ℕ)
    (U : (E.system n).base.Configuration) :
    E.renormalizedWilsonActionObservable scale offset n U =
      scale n * E.wilsonActionObservable n U + offset n :=
  rfl

/-- The Wilson-action observable is measurable on every finite compact-gauge
configuration space. -/
theorem ContinuousCompactGaugeWilsonPhysicalEmbedding.wilsonActionObservable_measurable
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (n : ℕ) :
    Measurable (E.wilsonActionObservable n) :=
  (ENNReal.continuous_ofReal.comp
    (continuous_compact_gauge_wilsonAction (E.system n))).measurable

/-- A finite uniform expectation bound for the unscaled Wilson actions. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionMomentBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) where
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ n,
      ∫⁻ U, E.wilsonActionObservable n U
        ∂((E.system n).gibbsProbabilityMeasure :
          Measure (E.system n).base.Configuration) ≤ momentBound

/-- Uniform upper bounds for the affine renormalization coefficients. -/
structure WilsonActionAffineCoefficientBounds
    (scale offset : ℕ → ENNReal) where
  scaleBound : ENNReal
  offsetBound : ENNReal
  scaleBound_ne_top : scaleBound ≠ ⊤
  offsetBound_ne_top : offsetBound ≠ ⊤
  scale_le : ∀ n, scale n ≤ scaleBound
  offset_le : ∀ n, offset n ≤ offsetBound

namespace WilsonActionAffineCoefficientBounds

/-- An unscaled action moment estimate and uniformly bounded affine
coefficients imply the renormalized Wilson-action control moment estimate. -/
def toWilsonActionControlMomentBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (M : E.WilsonActionMomentBound) :
    E.WilsonActionControlMomentBound scale offset :=
  { momentBound := C.scaleBound * M.momentBound + C.offsetBound
    momentBound_ne_top :=
      ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top C.scaleBound_ne_top M.momentBound_ne_top,
          C.offsetBound_ne_top⟩
    uniform_lintegral_le := by
      intro n
      letI : IsProbabilityMeasure (E.system n).gibbsMeasure :=
        continuous_compact_gauge_gibbsMeasure_isProbabilityMeasure (E.system n)
      have hActionMeas : Measurable (E.wilsonActionObservable n) :=
        E.wilsonActionObservable_measurable n
      have hScaledMeas :
          Measurable (fun U => scale n * E.wilsonActionObservable n U) :=
        measurable_const.mul hActionMeas
      calc
        ∫⁻ U,
            E.renormalizedWilsonActionObservable scale offset n U
            ∂((E.system n).gibbsProbabilityMeasure :
              Measure (E.system n).base.Configuration) =
            scale n *
                (∫⁻ U, E.wilsonActionObservable n U
                  ∂((E.system n).gibbsProbabilityMeasure :
                    Measure (E.system n).base.Configuration)) +
              offset n := by
                simp_rw [E.renormalizedWilsonActionObservable_eq]
                rw [lintegral_add_left hScaledMeas]
                rw [lintegral_const_mul _ hActionMeas]
                simp
        _ ≤ C.scaleBound * M.momentBound + C.offsetBound := by
          gcongr
          · exact C.scale_le n
          · exact M.uniform_lintegral_le n
          · exact C.offset_le n }

/-- The three concrete receipts—physical coercivity, an unscaled Wilson-action
moment bound, and bounded renormalization coefficients—imply tightness. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (M : E.WilsonActionMomentBound)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  D.isTight (C.toWilsonActionControlMomentBound M)

/-- The same three receipts produce a physical continuum weak limit. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (M : E.WilsonActionMomentBound)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit (C.toWilsonActionControlMomentBound M)

end WilsonActionAffineCoefficientBounds

noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_actionMoment
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (M : E.WilsonActionMomentBound)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  C.toWeakLimit M D

end

end MathlibAnalytic
end MGAP4D
