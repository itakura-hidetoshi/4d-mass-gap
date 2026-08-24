import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance approximatingBoundarySpatialSlicePairL2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance approximatingBoundarySpatialSlicePairL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance approximatingBoundarySpatialSlicePairL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance approximatingBoundarySpatialSlicePairL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance approximatingBoundarySpatialSlicePairL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance approximatingBoundarySpatialSlicePairL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-!
# Approximating Wilson OS boundary moments as two-slice kernels

The shared reflection-fixed boundary of an even periodic lattice consists of
*two* spatial slices: the primary and antipodal fixed time planes.  The exact
finite reindexing and Haar transport are already available in
`PeriodicHypercubicEvenBoundarySpatialSlicePair`.

This file turns that geometric fact into the Hilbert carrier naturally seen by
the finite Wilson OS boundary moment.  It deliberately does **not** identify
this two-slice carrier with the one-slice positive-half closure endpoint Hilbert
space.  Such an identification would require an additional concrete
factorization of the boundary kernel.
-/

/-- Real `L²` on the ordered primary/antipodal pair of spatial-slice
configurations.  This is the natural kernel carrier after the exact fixed-edge
reindexing. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundarySpatialSlicePairL2
    (H N : ℕ) : Type :=
  MeasureTheory.Lp ℝ 2
    (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N)

/-- The actual shared-boundary `L²` isometrically reindexed as a function on the
ordered primary/antipodal spatial-slice pair.

The map is composition with the inverse of the exact measurable boundary
coordinate equivalence.  No Hilbert-space identification is assumed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2LinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundarySpatialSlicePairL2 H N := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h : MeasurePreserving e
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar H N
  exact MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ e.symm
    (MeasurePreserving.symm e h)

/-- The reverse coordinate pullback from pair-slice `L²` to the original shared
boundary `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundarySpatialSlicePairL2ToBoundaryL2LinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundarySpatialSlicePairL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h : MeasurePreserving e
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar H N
  exact MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ e h

/-- One actual approximating Wilson OS boundary moment, expressed as an `L²`
kernel on the ordered pair `(primary slice, antipodal slice)`. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    PeriodicHypercubicEvenSpecialUnitaryBoundarySpatialSlicePairL2
      (halfExtent n) N :=
  periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2LinearIsometry
    (halfExtent n) N
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F hF)

/-- Pointwise meaning of the two-slice kernel, up to the canonical `L²`
almost-everywhere representative: evaluate the original shared-boundary moment
at the inverse primary/antipodal coordinate reindexing. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2_coeFn
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF =ᵐ[
          periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure (halfExtent n) N]
      fun z =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F
          ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv
            (halfExtent n) (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm z) := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv (halfExtent n)
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h : MeasurePreserving e
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
      (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure (halfExtent n) N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
        (halfExtent n) N
  let hsymm : MeasurePreserving e.symm
      (periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure (halfExtent n) N)
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) :=
    MeasurePreserving.symm e h
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
  unfold periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2LinearIsometry
  change
    MeasureTheory.Lp.compMeasurePreserving e.symm hsymm
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F hF) =ᵐ[_] _
  refine (MeasureTheory.Lp.coeFn_compMeasurePreserving
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F hF) hsymm).trans ?_
  exact hsymm.quasiMeasurePreserving.ae_le
    (hF.coeFn_toLp.fun_comp e.symm)

/-- Reindexing from the actual fixed boundary to the two spatial slices preserves
exactly the squared `L²` norm of every approximating Wilson OS boundary moment. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2_norm_sq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
  rw [LinearIsometry.norm_map]
  exact physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta B hInvariant n F hF

/-- The approximating OS quadratic value is exactly the squared norm of its
concrete two-spatial-slice boundary kernel.

This is a quadratic identification only.  The currently available weak-star
finite bridge does not assert linear compatibility of the chosen finite
positive-half observables, so no linear map from the full approximating OS
carrier is claimed here. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_boundarySpatialSlicePairL2_norm_sq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N))
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue F =
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF‖ ^ 2 := by
  rw [physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral]
  rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
    S D halfExtent N hN beta hbeta B hInvariant n F hf]
  exact
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F hF).symm

/-- Consequently, under the same concrete integrability hypotheses, an
approximating carrier has zero OS quadratic value exactly when its two-slice
boundary kernel vanishes in `L²`.

This is the precise null-space compatibility available before any additional
single-slice endpoint factorization theorem. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_zero_iff_boundarySpatialSlicePairL2_eq_zero
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N))
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue F = 0 ↔
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentSpatialSlicePairL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF = 0 := by
  rw [physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_boundarySpatialSlicePairL2_norm_sq
    S D halfExtent N hN beta hbeta B hInvariant n F hF hf]
  simp

end MathlibAnalytic
end MGAP4D

end