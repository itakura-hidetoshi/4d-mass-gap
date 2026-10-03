import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedProjectedNonTopProjectiveCarrier
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic

/-!
# A fixed projected non-top mode survives on an infinite scale subsequence

PR #5068 places both canonical projected two-mode excitations at every finite
Wilson scale in one fixed projective-limit continuum L² carrier. PR #5067
shows that at each scale at least one of the two images is nonzero.

Because the mode index is the finite type Fin 2, the infinite pigeonhole
principle removes the scale-dependent mode choice: one fixed mode is nonzero
at infinitely many scales. Since an infinite subset of the natural numbers is
order-isomorphic to ℕ, those scales can be enumerated by a strictly increasing
subsequence.

This is still purely kinematic. No convergence of the resulting common-carrier
subsequence is asserted. The next residual is compactness/Cauchy/coherence of
that fixed-mode subsequence, not mode selection.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance projectedFixedModeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance projectedFixedModeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance projectedFixedModeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance projectedFixedModeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectedFixedModeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance projectedFixedModeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance projectedFixedModeSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section FixedModeSubsequence

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

/-- Choose one nonzero projected mode at every finite scale. This choice is
only an intermediate device; the next theorem removes its scale dependence by
finite pigeonhole. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopNonzeroModeAtScale
    (n : ℕ) : Fin 2 :=
  (physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTopContinuumImage
    (hN2 := hN2) Q hInvariant R L n).choose

theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopNonzeroModeAtScale_ne_zero
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
        (hN2 := hN2) Q hInvariant R L
        (physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopNonzeroModeAtScale
          (hN2 := hN2) Q hInvariant R L n) n ≠ 0 :=
  (physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_projectedNonTopContinuumImage
    (hN2 := hN2) Q hInvariant R L n).choose_spec

/-- One fixed mode index is nonzero at infinitely many finite scales. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_fixedMode_infinite_nonzero_projectedScales :
    ∃ k : Fin 2,
      Set.Infinite
        {n : ℕ |
          physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
            (hN2 := hN2) Q hInvariant R L k n ≠ 0} := by
  let sel : ℕ → Fin 2 :=
    fun n =>
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopNonzeroModeAtScale
        (hN2 := hN2) Q hInvariant R L n
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber sel
  refine ⟨k, ?_⟩
  have hFiber : Set.Infinite (sel ⁻¹' ({k} : Set (Fin 2))) :=
    Set.infinite_coe_iff.1 hk
  apply hFiber.mono
  intro n hn
  have hsel : sel n = k := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hn
  change
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
      (hN2 := hN2) Q hInvariant R L k n ≠ 0
  rw [← hsel]
  simpa only [sel] using
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopNonzeroModeAtScale_ne_zero
      (hN2 := hN2) Q hInvariant R L n

/-- The infinitely many nonzero scales of one fixed mode can be enumerated by a
strictly increasing natural-number subsequence. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_fixedMode_strictMono_nonzero_projectedSubsequence :
    ∃ k : Fin 2, ∃ scale : ℕ → ℕ,
      StrictMono scale ∧
      ∀ j : ℕ,
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
          (hN2 := hN2) Q hInvariant R L k (scale j) ≠ 0 := by
  rcases
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_fixedMode_infinite_nonzero_projectedScales
      (hN2 := hN2) Q hInvariant R L with
    ⟨k, hk⟩
  let A : Set ℕ :=
    {n : ℕ |
      physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
        (hN2 := hN2) Q hInvariant R L k n ≠ 0}
  letI : Infinite A :=
    Set.Infinite.to_subtype (by simpa [A] using hk)
  let e : ℕ ≃o A := Nat.Subtype.orderIsoOfNat A
  let scale : ℕ → ℕ := fun j => (e j : ℕ)
  have hscale : StrictMono scale := by
    intro i j hij
    exact e.strictMono hij
  refine ⟨k, scale, hscale, ?_⟩
  intro j
  exact (e j).property

/-- Along the fixed-mode strictly increasing nonzero subsequence, every finite
preimage still satisfies the uniform q0^m estimate. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_fixedMode_strictMono_nonzero_projectedSubsequence_with_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ k : Fin 2, ∃ scale : ℕ → ℕ,
      StrictMono scale ∧
      ∀ j : ℕ,
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
            (hN2 := hN2) Q hInvariant R L k (scale j) ≠ 0 ∧
        ∀ m : ℕ,
          ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
              (halfExtent (scale j)) N hN (beta (scale j)) (hbeta (scale j)) ^ m)
              (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
                (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k (scale j))‖ ≤
            GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
              ‖physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
                (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k (scale j)‖ := by
  rcases
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_fixedMode_strictMono_nonzero_projectedSubsequence
      (hN2 := hN2) Q hInvariant R L with
    ⟨k, scale, hscale, hne⟩
  refine ⟨k, scale, hscale, ?_⟩
  intro j
  refine ⟨hne j, ?_⟩
  intro m
  exact
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_pow_norm_le_uniform_q0
      (hN2 := hN2) Q hInvariant s hs hcut k (scale j) m

end FixedModeSubsequence

end

end MathlibAnalytic
end MGAP4D
