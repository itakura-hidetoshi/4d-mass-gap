import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureOpenHalfContinuity
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe v

/-- Boundary-fibered assembly is jointly continuous in the shared boundary and
positive open-half coordinates when the negative open-half coordinate is fixed.

This is the two-variable strengthening of the existing separate boundary and
positive-coordinate continuity lemmas.  The proof is still purely
coordinatewise: positive edges read the second product coordinate, fixed edges
read the first product coordinate, and negative edges are constant. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_continuous_boundary_positive
    {Edge : Type} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [TopologicalSpace Value]
    (y : P.OpenHalfConfiguration Value) :
    Continuous
      (fun z : P.BoundaryConfiguration Value × P.OpenHalfConfiguration Value =>
        P.boundaryFiberedAssemble z.1 z.2 y) := by
  apply continuous_pi
  intro e
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos] using
      ((continuous_apply (⟨e, hpos⟩ : P.PositiveEdge)).comp continuous_snd :
        Continuous
          (fun z : P.BoundaryConfiguration Value × P.OpenHalfConfiguration Value =>
            z.2 ⟨e, hpos⟩))
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos, hneg]
      exact continuous_const
    · have hfixed : P.side e = ReflectionEdgeSide.fixed := by
        cases hside : P.side e <;> simp_all
      simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg, hfixed] using
        ((continuous_apply (⟨e, hfixed⟩ : P.FixedEdge)).comp continuous_fst :
          Continuous
            (fun z : P.BoundaryConfiguration Value × P.OpenHalfConfiguration Value =>
              z.1 ⟨e, hfixed⟩))

local instance boundaryCompletedPositiveJointContinuityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryCompletedPositiveJointContinuityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryCompletedPositiveJointContinuityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryCompletedPositiveJointContinuitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryCompletedPositiveJointContinuitySU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The completed positive Wilson amplitude is jointly continuous in the
physical shared-boundary and positive open-half coordinates.  Both the positive
bulk and boundary-adjacent temporal interactions remain present. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_continuous_boundary_openHalf
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
          H N beta z.1 z.2) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hAssemble : Continuous
      (fun z :
          P.BoundaryConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            P.OpenHalfConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble z.1 z.2 (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_boundary_positive (fun _ => 1)
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  exact
    (periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_continuous
      H N hN beta).comp hAssemble

/-- For SU(2), the actual completed-positive Gram feature is jointly continuous
in shared-boundary and positive open-half data.  Boundary dependence of the
square-root Gram coefficient uses the already-proved physical boundary
coefficient continuity; open-half dependence is carried by the completed Wilson
amplitude. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_boundary_openHalf
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta z.1 z.2) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  exact
    (Real.continuous_sqrt.comp
      ((periodicHypercubicEvenBoundaryGramCoefficient_continuous H beta hbeta).comp
        continuous_fst)).mul
    (periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_continuous_boundary_openHalf
      H 2 (by norm_num) beta)

/-- Bundle the fixed-boundary completed-positive Gram feature as an actual
continuous function on the positive open half. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2, ℝ) :=
  ⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 (by norm_num) beta hbeta b,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
      H 2 (by norm_num) beta hbeta b⟩

@[simp] theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2_apply
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
        H beta hbeta b x =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 (by norm_num) beta hbeta b x := rfl

/-- The fixed-boundary Gram feature varies continuously as a `ContinuousMap`
valued function of the boundary configuration.  Mathlib's compact-open curry
principle reduces this directly to the joint continuity theorem above; on the
compact finite open-half configuration space this is the function-space
continuity needed for the subsequent C⁰/Bochner integral layer. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
        H beta hbeta) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa [Function.uncurry,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2] using
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_boundary_openHalf
      H beta hbeta

end

end MathlibAnalytic
end MGAP4D
