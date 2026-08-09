import MGAP4D.MathlibAnalytic.FiniteProductProbabilityProjectiveFamily
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
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- Finite scale marginals are dependent products of the normalized boundary
Haar laws belonging to the finitely many selected Wilson scales. -/
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

/-- The actual common probability carrier: Mathlib's infinite product of the
boundary-Haar probability spaces indexed by Wilson scale. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
    (halfExtent : ℕ → ℕ) (N : ℕ) :
    Measure
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonBoundaryScaleConfiguration
          halfExtent N n) :=
  Measure.infinitePi
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n)

instance physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure_probability
    (halfExtent : ℕ → ℕ) (N : ℕ) :
    IsProbabilityMeasure
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
        halfExtent N) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
  infer_instance

/-- Mathlib's infinite product is a genuine projective limit of all finite
boundary-Haar scale marginals.  Thus projective-limit existence is theorem-
generated and no longer model-facing input. -/
theorem physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProduct_projectiveLimit
    (halfExtent : ℕ → ℕ) (N : ℕ) :
    IsProjectiveLimit
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
        halfExtent N)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleFiniteMarginal
        halfExtent N) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
  exact finiteProductProbabilityMarginal_infinitePi_projectiveLimit
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n)

/-- Evaluation at one Wilson scale is measure preserving from the actual
infinite-product carrier to that scale's boundary-Haar law. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleEvaluationMeasurePreserving
    (halfExtent : ℕ → ℕ) (N n : ℕ) :
    MeasurePreserving
      (Function.eval n)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
        halfExtent N)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N n) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
  exact measurePreserving_eval_infinitePi
    (fun k =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleHaarMeasure
        halfExtent N k)
    n

/-- Pull one finite boundary-Haar `L²` space directly into the common actual
infinite-product `L²` carrier. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryHaarL2ToScaleCommon
    (halfExtent : ℕ → ℕ) (N n : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
          halfExtent N) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (Function.eval n)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleEvaluationMeasurePreserving
      halfExtent N n)

@[simp] theorem physicalYangMillsEvenPeriodicWilsonBoundaryHaarL2ToScaleCommon_norm
    (halfExtent : ℕ → ℕ) (N n : ℕ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N) :
    ‖physicalYangMillsEvenPeriodicWilsonBoundaryHaarL2ToScaleCommon
        halfExtent N n f‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

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

/-- Mass-free kinematic common-carrier embedding of every completed finite
Wilson OS Hilbert space into the actual boundary-Haar scale infinite-product
`L²`.

The first factor is the already-proved OS quotient/completion boundary-moment
isometry.  The second is Mathlib pullback along a measure-preserving coordinate
evaluation.  No cross-scale interacting Gibbs projectivity, vacuum-gap
certificate, physical mass, or spectral input is used. -/
noncomputable def physicalHilbertBoundaryScaleCommonLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleInfiniteProductMeasure
          halfExtent N) :=
  (physicalYangMillsEvenPeriodicWilsonBoundaryHaarL2ToScaleCommon
      halfExtent N n).comp
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)

@[simp] theorem physicalHilbertBoundaryScaleCommonLinearIsometry_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖Q.physicalHilbertBoundaryScaleCommonLinearIsometry hInvariant n phi‖ =
      ‖phi‖ :=
  LinearIsometry.norm_map _ phi

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
