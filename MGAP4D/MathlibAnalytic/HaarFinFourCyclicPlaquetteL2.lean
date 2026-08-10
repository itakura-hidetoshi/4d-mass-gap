import MGAP4D.MathlibAnalytic.HaarPlaquetteWordL2Orthonormal
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u

/-- Canonical reshaping of four coordinates into the nested order expected by
`haarCyclicPlaquetteWord`.

Starting from the natural `Fin 4` order `(a,b,c,d)`, the resulting nested tuple
is `(((b,a),d),c)`.  The two adjacent swaps are performed already at the index
reindexing stage, so the measure proof uses only finite-product measurable
equivalences and product associativity. -/
noncomputable def haarFinFourCyclicNestedCoordinates
    {G : Type u} [MeasurableSpace G]
    (x : Fin 4 → G) : ((G × G) × G) × G :=
  let order : Fin 4 ≃ Fin 4 :=
    (Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap (2 : Fin 4) 3)
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin 2 ⊕ Fin 2 => G)
    (order.trans (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm)
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin 2 ⊕ Fin 2 => G)
  let pair := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G)
  (MeasurableEquiv.prodAssoc :
      ((G × G) × G) × G ≃ᵐ (G × G) × (G × G)).symm
    (Prod.map pair pair (split (reindex x)))

/-- Pointwise evaluation of the canonical `Fin 4` reshaping.

This isolates the concrete finite-coordinate computation from downstream
consumers: the measurable-equivalence implementation above evaluates exactly
to `(((x 1, x 0), x 3), x 2)`. -/
theorem haarFinFourCyclicNestedCoordinates_apply
    {G : Type u} [MeasurableSpace G]
    (x : Fin 4 → G) :
    haarFinFourCyclicNestedCoordinates x =
      (((x 1, x 0), x 3), x 2) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · simp [haarFinFourCyclicNestedCoordinates]
      · simp [haarFinFourCyclicNestedCoordinates]
    · simp [haarFinFourCyclicNestedCoordinates]
  · simp [haarFinFourCyclicNestedCoordinates]

/-- The canonical `Fin 4` Haar-product reshaping is measure-preserving.

The proof is a composition of Mathlib equivalences:

* `piCongrLeft` along the permutation sending the natural order
  `(a,b,c,d)` to `(b,a,d,c)` and then `Fin 4 ≃ Fin 2 ⊕ Fin 2`;
* `sumPiEquivProdPi`;
* `piFinTwo` on each pair;
* inverse product associativity.
-/
theorem measurePreserving_haarFinFourCyclicNestedCoordinates
    {G : Type u} [MeasurableSpace G]
    (μ : Measure G) [SFinite μ] [IsProbabilityMeasure μ] :
    MeasurePreserving haarFinFourCyclicNestedCoordinates
      (Measure.pi fun _ : Fin 4 => μ)
      (((μ.prod μ).prod μ).prod μ) := by
  let order : Fin 4 ≃ Fin 4 :=
    (Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap (2 : Fin 4) 3)
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin 2 ⊕ Fin 2 => G)
    (order.trans (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm)
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin 2 ⊕ Fin 2 => G)
  let pair := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G)
  have hReindex :
      MeasurePreserving reindex
        (Measure.pi fun _ : Fin 4 => μ)
        (Measure.pi fun _ : Fin 2 ⊕ Fin 2 => μ) := by
    simpa [reindex] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin 2 ⊕ Fin 2 => μ)
        (order.trans (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm))
  have hSplit :
      MeasurePreserving split
        (Measure.pi fun _ : Fin 2 ⊕ Fin 2 => μ)
        ((Measure.pi fun _ : Fin 2 => μ).prod
          (Measure.pi fun _ : Fin 2 => μ)) := by
    simpa [split] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : Fin 2 ⊕ Fin 2 => μ))
  have hPair :
      MeasurePreserving pair
        (Measure.pi fun _ : Fin 2 => μ) (μ.prod μ) := by
    simpa [pair] using
      (MeasureTheory.measurePreserving_piFinTwo
        (fun _ : Fin 2 => μ))
  have hPairs :
      MeasurePreserving (Prod.map pair pair)
        ((Measure.pi fun _ : Fin 2 => μ).prod
          (Measure.pi fun _ : Fin 2 => μ))
        ((μ.prod μ).prod (μ.prod μ)) :=
    hPair.prod hPair
  have hAssocForward :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          ((G × G) × G) × G ≃ᵐ (G × G) × (G × G))
        (((μ.prod μ).prod μ).prod μ)
        ((μ.prod μ).prod (μ.prod μ)) :=
    MeasureTheory.measurePreserving_prodAssoc (μ.prod μ) μ μ
  have hAssocBack :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          ((G × G) × G) × G ≃ᵐ (G × G) × (G × G)).symm
        ((μ.prod μ).prod (μ.prod μ))
        (((μ.prod μ).prod μ).prod μ) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc :
        ((G × G) × G) × G ≃ᵐ (G × G) × (G × G))
      hAssocForward
  simpa [haarFinFourCyclicNestedCoordinates, order, reindex, split, pair,
    Function.comp_def] using
    hAssocBack.comp (hPairs.comp (hSplit.comp hReindex))

/-- The cyclic plaquette word directly on the natural `Fin 4` coordinate
product.  The internal reshaping sends `(a,b,c,d)` to `(((b,a),d),c)`, so this
is exactly `c⁻¹ * d⁻¹ * a * b`. -/
def haarFinFourCyclicPlaquetteWord
    {G : Type u} [MeasurableSpace G] [Group G]
    (x : Fin 4 → G) : G :=
  haarCyclicPlaquetteWord (haarFinFourCyclicNestedCoordinates x)

/-- Four independent probability-Haar coordinates indexed by `Fin 4` push
forward through the cyclic plaquette word to Haar itself. -/
theorem measurePreserving_haarFinFourCyclicPlaquetteWord
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [MeasureTheory.Measure.IsMulLeftInvariant μ] :
    MeasurePreserving haarFinFourCyclicPlaquetteWord
      (Measure.pi fun _ : Fin 4 => μ) μ := by
  simpa [haarFinFourCyclicPlaquetteWord, Function.comp_def] using
    (measurePreserving_haarCyclicPlaquetteWord μ).comp
      (measurePreserving_haarFinFourCyclicNestedCoordinates μ)

/-- Exact real `L²` pullback from one Haar holonomy variable to four
independent `Fin 4` Haar edge coordinates. -/
noncomputable def haarFinFourCyclicPlaquetteWordL2Pullback
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [MeasureTheory.Measure.IsMulLeftInvariant μ] :
    Lp ℝ 2 μ →ₗᵢ[ℝ]
      Lp ℝ 2 (Measure.pi fun _ : Fin 4 => μ) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    haarFinFourCyclicPlaquetteWord
    (measurePreserving_haarFinFourCyclicPlaquetteWord μ)

/-- Orthonormal Haar modes remain orthonormal on the natural `Fin 4` edge
product after cyclic plaquette pullback. -/
theorem haarFinFourCyclicPlaquetteWordL2Pullback_orthonormal
    {G : Type u} [MeasurableSpace G] [Group G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G)
    [SFinite μ] [IsProbabilityMeasure μ]
    [MeasureTheory.Measure.IsMulLeftInvariant μ]
    {κ : Type*}
    (v : κ → Lp ℝ 2 μ)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ ((haarFinFourCyclicPlaquetteWordL2Pullback μ) ∘ v) :=
  hv.comp_linearIsometry (haarFinFourCyclicPlaquetteWordL2Pullback μ)

end

end MathlibAnalytic
end MGAP4D
