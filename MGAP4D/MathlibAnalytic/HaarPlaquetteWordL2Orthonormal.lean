import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open MeasureTheory.Measure

noncomputable section

universe u

/-- The oriented four-edge plaquette word on two pairs of group variables.

The grouping is chosen to mirror the measure-preserving proof:
first multiply the first pair, invert and multiply the second pair, then
multiply the two resulting Haar variables.  By associativity this is the
usual word `a * b * c⁻¹ * d⁻¹`. -/
def haarPlaquetteWord
    {G : Type u} [Group G]
    (z : (G × G) × (G × G)) : G :=
  (z.1.1 * z.1.2) * (z.2.1⁻¹ * z.2.2⁻¹)

/-- Multiplication of two independent probability-Haar variables is again
Haar.  This is obtained entirely from Mathlib's measure-preserving shear
`measurePreserving_prod_mul` followed by the probability projection to the
second coordinate. -/
theorem measurePreserving_haarPairMul
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] :
    MeasurePreserving (fun z : G × G => z.1 * z.2) (μ.prod μ) μ := by
  simpa [Function.comp_def] using
    (MeasureTheory.measurePreserving_snd.comp
      (MeasureTheory.measurePreserving_prod_mul μ μ))

/-- The product of inverses of two independent inversion-invariant Haar
variables is again Haar. -/
theorem measurePreserving_haarPairInvMul
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] [IsInvInvariant μ] :
    MeasurePreserving (fun z : G × G => z.1⁻¹ * z.2⁻¹) (μ.prod μ) μ := by
  have hInv :
      MeasurePreserving (Inv.inv : G → G) μ μ :=
    measurePreserving_inv μ
  have hInvPair :
      MeasurePreserving (Prod.map Inv.inv Inv.inv) (μ.prod μ) (μ.prod μ) :=
    hInv.prod hInv
  simpa [Function.comp_def] using
    (measurePreserving_haarPairMul μ).comp hInvPair

/-- Four independent probability-Haar variables pushed through the oriented
plaquette word `a * b * c⁻¹ * d⁻¹` have exactly the same Haar law.

No character theory, eigenvalue estimate, or explicit integration is used:
the result is a composition of Mathlib measure-preserving maps. -/
theorem measurePreserving_haarPlaquetteWord
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] [IsInvInvariant μ] :
    MeasurePreserving haarPlaquetteWord
      ((μ.prod μ).prod (μ.prod μ)) μ := by
  have hPair :
      MeasurePreserving
        (Prod.map
          (fun z : G × G => z.1 * z.2)
          (fun z : G × G => z.1⁻¹ * z.2⁻¹))
        ((μ.prod μ).prod (μ.prod μ)) (μ.prod μ) :=
    (measurePreserving_haarPairMul μ).prod
      (measurePreserving_haarPairInvMul μ)
  simpa [haarPlaquetteWord, Function.comp_def] using
    (measurePreserving_haarPairMul μ).comp hPair

/-- Pullback along the Haar plaquette word as an exact real `L²`
`LinearIsometry`.

This is the analytic bridge needed for gauge-invariant plaquette class
functions: every normalized-Haar `L²` mode on the holonomy variable can be
realized isometrically on four independent Haar edge variables. -/
noncomputable def haarPlaquetteWordL2Pullback
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] [IsInvInvariant μ] :
    Lp ℝ 2 μ →ₗᵢ[ℝ]
      Lp ℝ 2 ((μ.prod μ).prod (μ.prod μ)) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    haarPlaquetteWord
    (measurePreserving_haarPlaquetteWord μ)

/-- Orthonormal Haar modes remain orthonormal after pullback through the
four-edge plaquette holonomy word. -/
theorem haarPlaquetteWordL2Pullback_orthonormal
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] [IsInvInvariant μ]
    {κ : Type*}
    (v : κ → Lp ℝ 2 μ)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ ((haarPlaquetteWordL2Pullback μ) ∘ v) :=
  hv.comp_linearIsometry (haarPlaquetteWordL2Pullback μ)

end

end MathlibAnalytic
end MGAP4D
