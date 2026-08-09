import MGAP4D.MathlibAnalytic.RealL2MeasurePreservingConstant
import MGAP4D.MathlibAnalytic.FiniteProductProbabilityProjectiveFamily
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalProjectiveL2Carrier
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

/-- The reflection-fixed boundary configuration carried by the interacting
Wilson scale `n`.

This local abbreviation deliberately avoids importing the pure boundary-Haar
scale carrier solely for its coordinate type. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
    (halfExtent : ℕ → ℕ) (N : ℕ) (n : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
    (halfExtent n) N

/-- The actual interacting reflection-fixed boundary marginal at Wilson scale
`n`.  Unlike the pure-Haar common carrier, this coordinate law already absorbs
the squared finite OS boundary vacuum wavefunction. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) :
    Measure
      (PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
        halfExtent N n) :=
  periodicHypercubicEvenBoundaryMarginalMeasure
    (halfExtent n) N hN (beta n) (hbeta n)

/-- Every interacting boundary marginal is a probability measure because it is
exactly the pushforward of the normalized finite Wilson Gibbs law under
boundary restriction. -/
instance physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure_probability
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) :
    IsProbabilityMeasure
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n) := by
  change IsProbabilityMeasure
    (periodicHypercubicEvenBoundaryMarginalMeasure
      (halfExtent n) N hN (beta n) (hbeta n))
  let mp :=
    periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      (halfExtent n) N hN (beta n) (hbeta n)
  refine ⟨?_⟩
  rw [← mp.map_eq]
  rw [Measure.map_apply mp.measurable MeasurableSet.univ]
  simpa using
    (periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).measure_univ

/-- Finite products of the actual interacting boundary marginals.  Independence
here is a kinematic common-carrier device; it makes no claim that Wilson Gibbs
laws at different lattice spacings are exact coarse-graining marginals of one
another. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalFiniteProduct
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (J : Finset ℕ) :
    Measure
      (∀ n : J,
        PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
          halfExtent N n) :=
  finiteProductProbabilityMarginal
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n)
    J

/-- The finite interacting boundary products form an exact Mathlib projective
family. -/
theorem physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalFiniteProduct_projective
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    IsProjectiveMeasureFamily
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalFiniteProduct
        halfExtent N hN beta hbeta) := by
  exact finiteProductProbabilityMarginal_projective
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n)

/-- Actual mass-free common probability measure: the infinite product of all
interacting finite-Wilson boundary marginals. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    Measure
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
          halfExtent N n) :=
  Measure.infinitePi
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n)

instance physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct_probability
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    IsProbabilityMeasure
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
  infer_instance

/-- The infinite interacting product is the genuine projective limit of all
finite scale products. -/
theorem physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct_projectiveLimit
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    IsProjectiveLimit
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalFiniteProduct
        halfExtent N hN beta hbeta) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
  exact finiteProductProbabilityMarginal_infinitePi_projectiveLimit
    (fun n =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n)

/-- Coordinate evaluation from the common interacting product to one finite
boundary marginal is measure preserving. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalEvaluationMeasurePreserving
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) :
    MeasurePreserving
      (Function.eval n)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta n) := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
  exact measurePreserving_eval_infinitePi
    (fun k =>
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
        halfExtent N hN beta hbeta k)
    n

/-- Pull one interacting boundary-marginal `L²` space into the common infinite
product `L²`. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) :
    PeriodicHypercubicEvenBoundaryMarginalL2
        (halfExtent n) N hN (beta n) (hbeta n) →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
          halfExtent N hN beta hbeta) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (Function.eval n)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalEvaluationMeasurePreserving
      halfExtent N hN beta hbeta n)

/-- The common product's distinguished normalized vacuum candidate is the
canonical constant-one `L²` vector. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    Lp ℝ 2
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta) :=
  Lp.const 2
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
      halfExtent N hN beta hbeta)
    (1 : ℝ)

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

/-- Finite completed Wilson OS Hilbert space embedded into its actual
interacting boundary marginal.  The first factor is the completed boundary
moment isometry; the second is reciprocal multiplication by the strictly
positive finite OS boundary-vacuum moment. -/
noncomputable def physicalHilbertBoundaryMarginalLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryMarginalL2
        (halfExtent n) N hN (beta n) (hbeta n) :=
  (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
      (halfExtent n) N hN (beta n) (hbeta n)).comp
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)

@[simp] theorem physicalHilbertBoundaryMarginalLinearIsometry_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n phi‖ = ‖phi‖ :=
  LinearIsometry.norm_map _ phi

/-- Mass-free common-carrier isometry through the interacting boundary
marginals. -/
noncomputable def physicalHilbertInteractingBoundaryCommonLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
          halfExtent N hN beta hbeta) :=
  (physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon
      halfExtent N hN beta hbeta n).comp
    (Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n)

@[simp] theorem physicalHilbertInteractingBoundaryCommonLinearIsometry_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖Q.physicalHilbertInteractingBoundaryCommonLinearIsometry hInvariant n phi‖ =
      ‖phi‖ :=
  LinearIsometry.norm_map _ phi

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

/-- The one remaining kinematic normalization needed to identify all finite OS
vacua with the same constant-one vector after reciprocal-vacuum transport.

It is intentionally weaker and more transparent than assuming a common
physical Hilbert embedding: it states only that the already theorem-generated
finite boundary-marginal isometry sends the normalized OS vacuum to constant
one.  The current coherent positive-half pullback is real-linear but does not
store unitality, so this fact must not be silently inferred from its fields. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  finite_vacuum_eq_one :
    ∀ n,
      Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
        Lp.const 2
          (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
            halfExtent N hN beta hbeta n)
          (1 : ℝ)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Under only finite vacuum normalization, every scale's completed Wilson OS
vacuum lands on one and the same constant-one vector in the common interacting
boundary product `L²`. -/
theorem commonEmbedding_vacuum
    (V : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility
      Q hInvariant)
    (n : ℕ) :
    Q.physicalHilbertInteractingBoundaryCommonLinearIsometry hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta := by
  change
    physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon
        halfExtent N hN beta hbeta n
      (Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)) =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta
  rw [V.finite_vacuum_eq_one n]
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
  exact realL2_compMeasurePreserving_const_one
    (Function.eval n)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalEvaluationMeasurePreserving
      halfExtent N hN beta hbeta n)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalVacuumCompatibility

end

end MathlibAnalytic
end MGAP4D
