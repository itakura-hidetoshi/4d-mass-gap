import MGAP4D.MathlibAnalytic.FiniteProductProbabilityProjectiveFamily
import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2IsometricSystem
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Density
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The reflection-fixed boundary configuration carried by Wilson scale `n`.

Using the whole finite boundary configuration as one scale coordinate avoids
any false claim that interacting Wilson Gibbs laws at distinct lattice spacings
are exactly related by Wilson-action-preserving coarse graining. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonBoundaryScaleConfiguration
    (halfExtent : ℕ → ℕ) (N : ℕ) (n : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
    (halfExtent n) N

/-- Coordinate probability law for the scale projective carrier: the canonical
normalized boundary Haar product, not the interacting Gibbs marginal. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
    (halfExtent : ℕ → ℕ) (N : ℕ) (n : ℕ) :
    Measure
      (PhysicalYangMillsEvenPeriodicWilsonBoundaryScaleConfiguration
        halfExtent N n) :=
  periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N

instance physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure_probability
    (halfExtent : ℕ → ℕ) (N : ℕ) (n : ℕ) :
    IsProbabilityMeasure
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  infer_instance

/-- Finite scale marginals are just dependent products of the normalized
boundary Haar laws belonging to the finitely many selected Wilson scales. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
    (halfExtent : ℕ → ℕ) (N : ℕ)
    (J : Finset ℕ) :
    Measure
      (∀ n : J,
        PhysicalYangMillsEvenPeriodicWilsonBoundaryScaleConfiguration
          halfExtent N n) :=
  finiteProductProbabilityMarginal
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n)
    J

/-- The boundary-Haar finite scale laws are theorem-generated as an exact
projective family.  No interacting cross-scale Gibbs consistency is assumed. -/
theorem physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal_projective
    (halfExtent : ℕ → ℕ) (N : ℕ) :
    IsProjectiveMeasureFamily
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
        halfExtent N) := by
  exact finiteProductProbabilityMarginal_projective
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n)

/-- A genuine projective-limit probability carrier for all finite Wilson
boundary-Haar scale coordinates.

Existence of this pure probability object is deliberately separated from the
interacting Wilson dynamics and from the physical OS identification. -/
structure PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit
    (halfExtent : ℕ → ℕ) (N : ℕ) where
  continuumMeasure :
    Measure
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonBoundaryScaleConfiguration
          halfExtent N n)
  projectiveLimit :
    IsProjectiveLimit continuumMeasure
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
        halfExtent N)

namespace PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}

/-- Evaluation from the singleton scale marginal to the actual boundary
configuration at that scale is measure preserving. -/
noncomputable def singletonEvaluationMeasurePreserving
    (n : ℕ) :
    MeasurePreserving
      (Function.eval
        (⟨n, by simp⟩ : ({n} : Finset ℕ)))
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
        halfExtent N {n})
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n) := by
  simpa [physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal,
    finiteProductProbabilityMarginal] using
    (MeasureTheory.measurePreserving_eval
      (μ := fun j : ({n} : Finset ℕ) =>
        physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
          halfExtent N j)
      (⟨n, by simp⟩ : ({n} : Finset ℕ)))

/-- Pull one actual boundary-Haar `L²` space into the corresponding singleton
scale marginal. -/
noncomputable def singletonBoundaryHaarL2Pullback
    (n : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
          halfExtent N {n}) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (Function.eval (⟨n, by simp⟩ : ({n} : Finset ℕ)))
    (singletonEvaluationMeasurePreserving (halfExtent := halfExtent) (N := N) n)

@[simp] theorem singletonBoundaryHaarL2Pullback_norm
    (n : ℕ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N) :
    ‖singletonBoundaryHaarL2Pullback
        (halfExtent := halfExtent) (N := N) n f‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

/-- Canonical isometric pullback of a singleton boundary-Haar scale marginal
into the common projective-limit `L²` carrier. -/
noncomputable def singletonMarginalToCommonL2
    (L : PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit
      halfExtent N)
    (n : ℕ) :
    Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
          halfExtent N {n}) →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  projectiveLimitFiniteMarginalL2Pullback
    L.continuumMeasure
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
      halfExtent N)
    L.projectiveLimit
    {n}

@[simp] theorem singletonMarginalToCommonL2_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit
      halfExtent N)
    (n : ℕ)
    (f : Lp ℝ 2
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
        halfExtent N {n})) :
    ‖L.singletonMarginalToCommonL2 n f‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

end PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Actual completed finite Wilson OS Hilbert space embedded into the singleton
boundary-Haar scale marginal.

The first factor is the already-proved OS quotient/completion boundary-moment
isometry; the second is only probability-measure pullback. -/
noncomputable def physicalHilbertSingletonBoundaryScaleLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
          halfExtent N {n}) :=
  (PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit.singletonBoundaryHaarL2Pullback
      (halfExtent := halfExtent) (N := N) n).comp
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)

@[simp] theorem physicalHilbertSingletonBoundaryScaleLinearIsometry_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖Q.physicalHilbertSingletonBoundaryScaleLinearIsometry hInvariant n phi‖ =
      ‖phi‖ :=
  LinearIsometry.norm_map _ phi

/-- Mass-free kinematic common-carrier embedding of every completed finite
Wilson OS Hilbert space into one boundary-Haar scale projective-limit `L²`.

Crucially, this construction uses no cross-scale interacting Gibbs
projectivity, no vacuum-gap certificate, no physical mass, and no spectral
input. -/
noncomputable def physicalHilbertBoundaryScaleCommonLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (L : PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit
      halfExtent N)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.singletonMarginalToCommonL2 n).comp
    (Q.physicalHilbertSingletonBoundaryScaleLinearIsometry hInvariant n)

@[simp] theorem physicalHilbertBoundaryScaleCommonLinearIsometry_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (L : PhysicalYangMillsEvenPeriodicWilsonBoundaryHaarScaleProjectiveLimit
      halfExtent N)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖Q.physicalHilbertBoundaryScaleCommonLinearIsometry hInvariant L n phi‖ =
      ‖phi‖ :=
  LinearIsometry.norm_map _ phi

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
