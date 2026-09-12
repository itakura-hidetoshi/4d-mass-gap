import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisL2Nonzero
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryNormalizedTracePolynomialHaarL2RepresentativeMarginalFinite
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenBoundaryMarginalMeasure H 2
        boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
        beta hbeta) := by
  rw [← periodicHypercubicEvenSpecialUnitary_map_boundaryRestriction_gibbsMeasure
    H 2 boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive beta hbeta]
  let mu :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2
      boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
      beta hbeta).gibbsMeasure
  change IsFiniteMeasure
    (Measure.map (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction mu)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
      (PeriodicHypercubicEvenSideLength H) 2
      boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
      beta hbeta
  letI : IsFiniteMeasure mu := ⟨by simp⟩
  exact Measure.isFiniteMeasure_map mu
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction

/-- The interacting-boundary normalized-trace polynomial vector is exactly the
`ContinuousMap.toLp` image of the polynomial continuous map.  This is only the
linearity of `toLp`; no new density or approximation is introduced. -/
theorem
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2_eq_toLp
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        H beta hbeta k c =
      ContinuousMap.toLp (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure H 2
          boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
          beta hbeta) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
          H k c) := by
  simp [periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2,
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial]

/-- The interacting-boundary polynomial vector has the expected pointwise
polynomial representative almost everywhere. -/
theorem periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2_coeFn
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        H beta hbeta k c =ᵐ[
          periodicHypercubicEvenBoundaryMarginalMeasure H 2
            boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
            beta hbeta]
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
        H k c := by
  rw [periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2_eq_toLp]
  exact ContinuousMap.coeFn_toLp
    (p := (2 : ℝ≥0∞))
    (μ := periodicHypercubicEvenBoundaryMarginalMeasure H 2
      boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
      beta hbeta)
    (𝕜 := ℝ)
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c)

/-- The actual boundary-Haar polynomial input used by the Wilson analysis
operator is represented almost everywhere by the square-root vacuum transport
`ψ_boundary * p`.  This closes the pointwise identification between the
existing analysis input and the raw integral representative without replacing
or weakening the interacting marginal. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_coeFn
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        H beta hbeta k c =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
      fun b =>
        periodicHypercubicEvenBoundaryVacuumMoment H 2
            boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
            beta hbeta b *
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
            H k c b := by
  let g := periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
    H beta hbeta k c
  have htransport :=
    periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H 2 boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
      beta hbeta g
  have hpolyMarg :=
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2_coeFn
      H beta hbeta k c
  have hpolyHaar :=
    periodicHypercubicEven_ae_marginal_to_boundaryHaar
      H 2 boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
      beta hbeta hpolyMarg
  have htransport' :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
        periodicHypercubicEvenBoundaryMarginalToHaarL2Function
          H 2 boundaryNormalizedTracePolynomialHaarL2RepresentativeTwoRankPositive
          beta hbeta g := by
    simpa [periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2, g]
      using htransport
  filter_upwards [htransport', hpolyHaar] with b ht hp
  rw [ht]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  rw [hp]

end

end MathlibAnalytic
end MGAP4D
