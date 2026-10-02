import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5UnfixedPathKernelMomentCriterion
import Mathlib.Tactic

/-!
# Pure unfixed path-kernel criterion for vacuum-normalized H1-D5

The preceding reduction writes the finite OS vacuum as

`Z^{-1/2} M_H`,

where `M_H` is the complete unfixed positive-half path-kernel moment in
ordered boundary-pair coordinates.

Both sides of the remaining H1-D5 scalar identity are real-linear in this
source.  The finite Wilson partition function is strictly positive, hence
`Z^{-1/2} != 0`.  The common scalar can therefore be cancelled exactly.

The resulting criterion contains no completed transfer, no semigroup-family
data on the right, no boundary Gram feature, and no partition normalization:
it is a pure finite Wilson one-slab-kernel identity for the unnormalized
positive-half path-kernel vacuum message.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PurePathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PurePathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PurePathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PurePathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PurePathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PurePathSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PurePathPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Left matrix coefficient in the literal H1-D5 Wilson criterion for an
arbitrary scalar source representative on pair-Haar space. -/
def periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ℝ :=
  (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2)⁻¹ *
    ∫ q, ∫ p,
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta (p, q))
        (phi p *
          (((x :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.1) *
            ((y :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  H N)) q.2)))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- Right matrix coefficient in the literal H1-D5 Wilson criterion for an
arbitrary scalar source representative on pair-Haar space. -/
def periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
    (H N : ℕ)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ℝ :=
  ∫ q,
    inner ℝ (phi q)
      (((x :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.1) *
        ((y :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.2))
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The raw Wilson coefficient is linear under pointwise real scaling of its
source representative. -/
theorem periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient_scale_source
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : ℝ)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
        H N hN beta hbeta (fun p => c * phi p) x y =
      c *
        periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
          H N hN beta hbeta phi x y := by
  unfold periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let a :=
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2)⁻¹
  let F := fun
      (q p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta (p, q))
      (phi p *
        (((x :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                H N)) q.1) *
          ((y :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                H N)) q.2)))
  have hpoint : ∀ q p,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (p, q))
          ((c * phi p) *
            (((x :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    H N)) q.1) *
              ((y :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    H N)) q.2))) =
        c * F q p := by
    intro q p
    dsimp [F]
    rw [realScalarInner_eq_mul, realScalarInner_eq_mul]
    ring
  calc
    a * (∫ q, ∫ p,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (p, q))
          ((c * phi p) *
            (((x :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    H N)) q.1) *
              ((y :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    H N)) q.2)))
      ∂mu ∂mu) =
        a * (∫ q, ∫ p, c * F q p ∂mu ∂mu) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with q
      apply integral_congr_ae
      filter_upwards with p
      exact hpoint q p
    _ = a * (∫ q, c * (∫ p, F q p ∂mu) ∂mu) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with q
      rw [integral_const_mul]
    _ = a * (c * (∫ q, ∫ p, F q p ∂mu ∂mu)) := by
      rw [integral_const_mul]
    _ = c * (a * (∫ q, ∫ p, F q p ∂mu ∂mu)) := by ring
    _ = c *
        ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2)⁻¹ *
          ∫ q, ∫ p,
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                H N beta (p, q))
              (phi p *
                (((x :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        H N)) q.1) *
                  ((y :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        H N)) q.2)))
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
      rfl

/-- The ordinary pair-Haar coefficient is linear under pointwise real scaling
of its source representative. -/
theorem periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_scale_source
    (H N : ℕ)
    (c : ℝ)
    (phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (x y :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
        H N (fun q => c * phi q) x y =
      c *
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N phi x y := by
  unfold periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let F := fun
      q :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    inner ℝ (phi q)
      (((x :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.1) *
        ((y :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.2))
  calc
    (∫ q,
      inner ℝ (c * phi q)
        (((x :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.1) *
          ((y :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.2))
      ∂mu) =
        ∫ q, c * F q ∂mu := by
      apply integral_congr_ae
      filter_upwards with q
      dsimp [F]
      rw [realScalarInner_eq_mul, realScalarInner_eq_mul]
      ring
    _ = c * ∫ q, F q ∂mu := by
      rw [integral_const_mul]
    _ = c *
        (∫ q,
          inner ℝ (phi q)
            (((x :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.1) *
              ((y :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) q.2))
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
      rfl

section VacuumNormalizedH1D5PurePath

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- Final scalar reduction of H1-D5 before the finite-path Markov recursion:
completed-transfer compatibility is equivalent to a pure unnormalized
positive-half path-kernel identity. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_pureUnfixedPathKernelMoment :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
              (halfExtent n) N hN (beta n) (hbeta n)
              (periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
                (halfExtent n) N (beta n))
              x y =
            periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
              (halfExtent n) N
              (periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
                (halfExtent n) N (beta n))
              x y := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentWilsonIntegral
      Q hInvariant C]
  constructor
  · intro h n x y
    let H := halfExtent n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        H N (beta n)
    let c :=
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN
            (beta n) (hbeta n)).base.partitionFunction)⁻¹
    have hZ :
        0 <
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN
              (beta n) (hbeta n)).base.partitionFunction :=
      compact_oriented_partitionFunction_pos
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN
            (beta n) (hbeta n)).base
        (continuous_compact_oriented_boltzmannIntegrable
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN
              (beta n) (hbeta n)))
    have hc : c ≠ 0 := by
      exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hZ))
    have hxy := h n x y
    change
      periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
          H N hN (beta n) (hbeta n) (fun p => c * phi p) x y =
        periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
          H N (fun q => c * phi q) x y at hxy
    rw [
      periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient_scale_source,
      periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_scale_source
    ] at hxy
    exact mul_left_cancel₀ hc hxy
  · intro h n x y
    let H := halfExtent n
    let phi :=
      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
        H N (beta n)
    let c :=
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN
            (beta n) (hbeta n)).base.partitionFunction)⁻¹
    have hxy := h n x y
    have hscaled :
        c *
            periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient
              H N hN (beta n) (hbeta n) phi x y =
          c *
            periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient
              H N phi x y :=
      congrArg (fun z : ℝ => c * z) hxy
    rw [
      ← periodicHypercubicEvenSpecialUnitaryH1D5RawPairWilsonCoefficient_scale_source,
      ← periodicHypercubicEvenSpecialUnitaryH1D5PairHaarCoefficient_scale_source
    ] at hscaled
    change
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN (beta n) (hbeta n)‖ ^ 2)⁻¹ *
            ∫ q, ∫ p,
              inner ℝ
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                  H N (beta n) (p, q))
                ((c * phi p) *
                  (((x :
                      Lp ℝ 2
                        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                          H N)) q.1) *
                    ((y :
                      Lp ℝ 2
                        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                          H N)) q.2)))
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
          ∫ q,
            inner ℝ (c * phi q)
              (((x :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.1) *
                ((y :
                  Lp ℝ 2
                    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                      H N)) q.2))
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) at hscaled
    simpa [H, phi, c] using hscaled

end VacuumNormalizedH1D5PurePath

end

end MathlibAnalytic
end MGAP4D
