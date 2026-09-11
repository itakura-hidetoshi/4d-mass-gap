import MGAP4D.MathlibAnalytic.FiniteProductProbabilityEmbeddingRestrictionL2
import MGAP4D.MathlibAnalytic.HaarFinFourCyclicPlaquetteL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteFixedEdges

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance primaryPlaquetteBoundaryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryPlaquetteBoundaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryPlaquetteBoundarySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryPlaquetteBoundaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryPlaquetteBoundaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance primaryPlaquetteBoundaryHaarLeftInvariant (N : ℕ) :
    MeasureTheory.Measure.IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  unfold normalizedCompactHaar
  infer_instance

/-- Real `L²` of the four normalized-Haar `SU(N)` variables attached to the
canonical primary spatial plaquette. -/
abbrev PeriodicHypercubicEvenPrimarySpatialPlaquetteFourEdgeHaarL2
    (N : ℕ) :=
  Lp ℝ 2
    (Measure.pi fun _ : Fin 4 =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Pull the four independent normalized-Haar variables of the canonical
primary spatial plaquette isometrically into the actual full reflection-fixed
boundary Haar `L²`.

The only geometric input is the theorem-generated embedding of the four
distinct plaquette links into the actual fixed-edge index from #1612. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryL2Pullback
    (H N : ℕ) :
    PeriodicHypercubicEvenPrimarySpatialPlaquetteFourEdgeHaarL2 N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  change Lp ℝ 2 (Measure.pi fun _ : Fin 4 => μ) →ₗᵢ[ℝ]
    Lp ℝ 2 (Measure.pi fun _ : P.FixedEdge => μ)
  exact finiteProductProbabilityEmbeddingRestrictionL2Pullback μ
    (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H)

/-- Four-edge normalized-Haar orthonormality survives exactly after embedding
into the full actual boundary Haar product. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryL2Pullback_orthonormal
    (H N : ℕ)
    {κ : Type*}
    (v : κ → PeriodicHypercubicEvenPrimarySpatialPlaquetteFourEdgeHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryL2Pullback H N) ∘ v) :=
  hv.comp_linearIsometry
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryL2Pullback H N)

/-- The canonical cyclic plaquette holonomy read directly from the actual
reflection-fixed boundary configuration.

If the four oriented physical edge values in natural boundary order are
`(a,b,c,d)`, this map is `c⁻¹ * d⁻¹ * a * b`.  It is the cyclic conjugate of
the actual oriented Wilson plaquette holonomy `a * b * c⁻¹ * d⁻¹`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  haarFinFourCyclicPlaquetteWord
    (fun k => b
      (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))

/-- Under the actual full boundary normalized-Haar product, the canonical
primary spatial plaquette cyclic holonomy is itself exactly normalized Haar.

This is the composition of the theorem-generated four-edge coordinate
restriction with the generic cyclic Haar-word theorem; no direct four-fold
integral calculation is used. -/
theorem measurePreserving_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hEdges :
      MeasurePreserving
        (fun (b : P.BoundaryConfiguration
            (Matrix.specialUnitaryGroup (Fin N) ℂ)) (k : Fin 4) =>
          b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))
        (Measure.pi fun _ : P.FixedEdge => μ)
        (Measure.pi fun _ : Fin 4 => μ) :=
    measurePreserving_finiteProductProbabilityEmbeddingRestriction μ
      (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H)
  have hWord :
      MeasurePreserving
        (haarFinFourCyclicPlaquetteWord :
          (Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) →
            Matrix.specialUnitaryGroup (Fin N) ℂ)
        (Measure.pi fun _ : Fin 4 => μ) μ :=
    measurePreserving_haarFinFourCyclicPlaquetteWord μ
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy,
    P, μ, Function.comp_def] using hWord.comp hEdges

/-- Exact real `L²` realization of a single normalized-Haar `SU(N)` holonomy
mode as a function of the actual canonical primary spatial plaquette inside the
full boundary Haar product. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback
    (H N : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N)
    (measurePreserving_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N)

/-- Every normalized-Haar orthonormal holonomy family remains orthonormal after
realization on the actual canonical primary spatial plaquette in full boundary
Haar `L²`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback_orthonormal
    (H N : ℕ)
    {κ : Type*}
    (v : κ → SpecialUnitaryNormalizedHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H N) ∘ v) :=
  hv.comp_linearIsometry
    (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H N)

end

end MathlibAnalytic
end MGAP4D
