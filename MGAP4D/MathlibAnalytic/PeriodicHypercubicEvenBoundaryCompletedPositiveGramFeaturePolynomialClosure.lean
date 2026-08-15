import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureOpenHalfContinuity
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology

noncomputable section

local instance boundaryPositiveGramPolynomialClosureNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveGramPolynomialClosureTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPositiveGramPolynomialClosureCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- The continuous function `x ↦ exp (-β f x)`.  This small bundled wrapper is
used to expose Mathlib's one-variable polynomial approximation theorem without
introducing any global density hypothesis on the ambient configuration space. -/
private noncomputable def continuousMapNegBetaExp
    {X : Type*} [TopologicalSpace X]
    (beta : ℝ) (f : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => Real.exp (-beta * f x),
    Real.continuous_exp.comp (continuous_const.mul f.continuous)⟩

/-- If a real continuous observable belongs to a subalgebra on a compact
configuration space, its Wilson-type exponential `exp (-β f)` belongs to the
uniform closure of the same subalgebra.

This is the precise Mathlib replacement for an ad hoc Taylor-series argument:
`ContinuousMap.comp_attachBound_mem_closure` first attaches the compact range
`[-‖f‖, ‖f‖]` and then applies polynomial approximation there. -/
private theorem continuousMapNegBetaExp_mem_topologicalClosure
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ))
    (beta : ℝ) (f : C(X, ℝ)) (hf : f ∈ A) :
    continuousMapNegBetaExp beta f ∈ A.topologicalClosure := by
  let fA : A := ⟨f, hf⟩
  let p : C(Set.Icc (-‖fA‖) ‖fA‖, ℝ) :=
    ⟨fun t => Real.exp (-beta * (t : ℝ)),
      Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)⟩
  have h := ContinuousMap.comp_attachBound_mem_closure A fA p
  have hp :
      p.comp (↑fA).attachBound = continuousMapNegBetaExp beta f := by
    ext x
    simp [p, fA, continuousMapNegBetaExp]
  rw [hp] at h
  exact h

/-- The strict-positive Wilson action, restricted to one actual positive
open-half fiber with fixed boundary data, as a bundled continuous function. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hAssemble : Continuous
      (fun x : P.OpenHalfConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble b x (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_positive b (fun _ => 1)
  exact
    ⟨fun x => periodicHypercubicEvenPositiveWilsonAction H N
        (P.boundaryFiberedAssemble b x (fun _ => 1)),
      (periodicHypercubicEvenPositiveWilsonAction_continuous H N hN).comp hAssemble⟩

/-- The positive-boundary-adjacent temporal Wilson action on the same actual
positive open-half fiber, bundled as a continuous function. -/
noncomputable def
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hAssemble : Continuous
      (fun x : P.OpenHalfConfiguration (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        P.boundaryFiberedAssemble b x (fun _ => 1)) :=
    P.boundaryFiberedAssemble_continuous_positive b (fun _ => 1)
  exact
    ⟨fun x => periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
        (P.boundaryFiberedAssemble b x (fun _ => 1)),
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_continuous
        H N hN).comp hAssemble⟩

/-- The actual completed-positive Wilson amplitude on a fixed boundary fiber as
a bundled continuous function. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ) :=
  ⟨periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b,
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_continuous_openHalf
      H N hN beta b⟩

/-- No density assumption is needed to obtain the Gibbs factor.  If a concrete
finite Wilson/cylinder subalgebra contains the two finite Wilson actions that
actually occur in the positive half, then the complete positive Gibbs amplitude
belongs to its sup-norm closure.

Both interaction sectors are retained.  The proof uses Mathlib's polynomial
approximation on the compact range of each action and closure under
multiplication. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap_mem_topologicalClosure_of_actions_mem
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (A : Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ))
    (hBulk :
      periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b ∈ A)
    (hTemporal :
      periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
        H N hN b ∈ A) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap
        H N hN beta b ∈ A.topologicalClosure := by
  let fBulk :=
    periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b
  let fTemporal :=
    periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
      H N hN b
  have hBulkClosure : continuousMapNegBetaExp beta fBulk ∈ A.topologicalClosure :=
    continuousMapNegBetaExp_mem_topologicalClosure A beta fBulk (by
      simpa [fBulk] using hBulk)
  have hTemporalClosure :
      continuousMapNegBetaExp beta fTemporal ∈ A.topologicalClosure :=
    continuousMapNegBetaExp_mem_topologicalClosure A beta fTemporal (by
      simpa [fTemporal] using hTemporal)
  have hMul :
      continuousMapNegBetaExp beta fBulk *
          continuousMapNegBetaExp beta fTemporal ∈ A.topologicalClosure :=
    A.topologicalClosure.mul_mem hBulkClosure hTemporalClosure
  have hProduct :
      continuousMapNegBetaExp beta fBulk *
          continuousMapNegBetaExp beta fTemporal =
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap
          H N hN beta b := by
    ext x
    simp [fBulk, fTemporal, continuousMapNegBetaExp,
      periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap,
      periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap,
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap,
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude,
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude,
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight]
  rw [hProduct] at hMul
  exact hMul

/-- The actual completed-positive Gram feature `K(b,·)` is therefore in the
same uniform closure.  The square-root boundary Gram coefficient is independent
of the open-half variable, so it is absorbed by scalar closure; no positivity
or density hypothesis beyond the already-proved finite-volume Wilson data is
added here. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_topologicalClosure_of_actions_mem
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (A : Subalgebra ℝ
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ))
    (hBulk :
      periodicHypercubicEvenBoundaryPositiveWilsonActionContinuousMap H N hN b ∈ A)
    (hTemporal :
      periodicHypercubicEvenBoundaryPositiveBoundaryTemporalWilsonActionContinuousMap
        H N hN b ∈ A) :
    (⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
        H N hN beta hbeta b⟩ :
      C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ)) ∈ A.topologicalClosure := by
  have hAmplitude :=
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap_mem_topologicalClosure_of_actions_mem
      H N hN beta b A hBulk hTemporal
  have hScaled := A.topologicalClosure.smul_mem
    (Real.sqrt (periodicHypercubicEvenBoundaryGramCoefficient
      H N hN beta hbeta b)) hAmplitude
  have hScaleEq :
      (Real.sqrt (periodicHypercubicEvenBoundaryGramCoefficient
          H N hN beta hbeta b)) •
        periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap
          H N hN beta b =
      (⟨periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_continuous_openHalf
          H N hN beta hbeta b⟩ :
        C((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
            (Matrix.specialUnitaryGroup (Fin N) ℂ), ℝ)) := by
    ext x
    simp [periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitudeContinuousMap,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature]
  rw [hScaleEq] at hScaled
  exact hScaled

end

end MathlibAnalytic
end MGAP4D
