import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredPairNonTopProjectionNonzero
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryHaarProjectiveCylinderOrthonormal
import Mathlib.Tactic

/-!
# Canonical common projective carrier for physical non-top projected excitations

PR #5067 closes the finite-volume side: at every scale there is a nonzero
vacuum-normalized two-mode excitation after orthogonal projection to the full
physical non-top block, and that projected vector satisfies the uniform q0^m
bound.

The finite projected vectors still live in different pair-Haar L² spaces.
This file moves them, without adding any compatibility assumption, into the
single projective-limit continuum L² carrier.

For each finite scale we use the exact chain of theorem-generated linear
isometries

  pair Haar L²
    -> shared boundary Haar L²
    -> interacting projective finite marginal L²
    -> projective-limit continuum L².

Hence norm and nonvanishing are preserved exactly.  In particular, at every
finite scale at least one of the two projected modes has a nonzero image in the
same continuum carrier.

No claim of scale coherence or convergence is made here.  After this file the
remaining continuum-facing problem can be stated entirely inside one fixed
Hilbert space.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Exact linear isometry from the ordered physical pair-Haar L² carrier at
one Wilson scale into the single projective-limit continuum L² carrier. -/
noncomputable def spatialSlicePairHaarProjectiveContinuumL2Isometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) N →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.finiteMarginalL2Pullback (R.marginalIndex n)).comp
    ((R.boundaryHaarProjectiveL2Isometry n).comp
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) N))

@[simp] theorem spatialSlicePairHaarProjectiveContinuumL2Isometry_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) N) :
    ‖R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n x‖ = ‖x‖ :=
  (R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n).norm_map x

@[simp] theorem spatialSlicePairHaarProjectiveContinuumL2Isometry_inner
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (n : ℕ)
    (x y :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) N) :
    inner ℝ
        (R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n x)
        (R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n y) =
      inner ℝ x y :=
  (R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n).inner_map_map x y

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

local instance projectedCommonCarrierTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance projectedCommonCarrierCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance projectedCommonCarrierSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance projectedCommonCarrierMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectedCommonCarrierBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance projectedCommonCarrierSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance projectedCommonCarrierSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section ProjectedNonTopCommonCarrier

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- The canonical continuum-carrier image of the physical non-top projection
of one actual vacuum-normalized centered two-mode pair. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
    (k : Fin 2) (n : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
    (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
      (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n)

/-- Moving a projected non-top excitation into the common projective carrier
preserves its norm exactly. -/
@[simp] theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_norm
    (k : Fin 2) (n : ℕ) :
    ‖physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
        (hN2 := hN2) Q hInvariant R L k n‖ =
      ‖physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n‖ := by
  exact
    R.spatialSlicePairHaarProjectiveContinuumL2Isometry_norm L n
      (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n)

/-- Nonvanishing is reflected exactly by the common-carrier embedding. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_ne_zero_iff
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
        (hN2 := hN2) Q hInvariant R L k n ≠ 0 ↔
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
        (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n ≠ 0 := by
  let I :=
    R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
  let x :=
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
      (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n
  change I x ≠ 0 ↔ x ≠ 0
  constructor
  · intro hIx hx
    apply hIx
    rw [hx, map_zero]
  · intro hx hIx
    apply hx
    apply I.injective
    simpa using hIx

/-- At every finite Wilson scale at least one of the two canonical projected
modes has a nonzero representative in the same continuum projective L²
carrier. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTopContinuumImage
    (n : ℕ) :
    ∃ k : Fin 2,
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
        (hN2 := hN2) Q hInvariant R L k n ≠ 0 := by
  rcases
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_centeredBoundaryPairNonTopProjection
      (hN2 := hN2) Q hInvariant n with
    ⟨k, hk⟩
  exact
    ⟨k,
      (physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_ne_zero_iff
        (hN2 := hN2) Q hInvariant R L k n).2 hk⟩

/-- Common-carrier finite-side package: at every scale there is a nonzero
continuum-carrier representative whose finite preimage is in the physical
non-top receiver and obeys the uniform q0^m estimate for all discrete powers.

The q0 dynamics is deliberately left on the authoritative finite physical pair
operator.  No continuum dynamics is identified here. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTopContinuumImage_with_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ) :
    ∃ k : Fin 2,
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
          (hN2 := hN2) Q hInvariant R L k n ≠ 0 ∧
      ∀ m : ℕ,
        ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) ^ m)
            (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
              (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n)‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
            ‖physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
              (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n‖ := by
  rcases
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_nonTopProjection_with_uniform_q0
      (hN2 := hN2) Q hInvariant s hs hcut n with
    ⟨k, hk, hq0⟩
  refine ⟨k, ?_, hq0⟩
  exact
    (physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_ne_zero_iff
      (hN2 := hN2) Q hInvariant R L k n).2 hk

end ProjectedNonTopCommonCarrier

end

end MathlibAnalytic
end MGAP4D
