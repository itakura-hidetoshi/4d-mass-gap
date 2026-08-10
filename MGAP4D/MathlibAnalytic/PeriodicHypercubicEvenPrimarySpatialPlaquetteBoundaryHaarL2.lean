import MGAP4D.MathlibAnalytic.FiniteProductProbabilityEmbeddingRestrictionL2
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

end

end MathlibAnalytic
end MGAP4D
