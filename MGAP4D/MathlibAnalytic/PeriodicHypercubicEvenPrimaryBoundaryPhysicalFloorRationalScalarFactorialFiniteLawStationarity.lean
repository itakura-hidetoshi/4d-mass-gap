import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalFactorialSubsequenceAlignment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalAlignedFiniteReadoutStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathWeakLimitOS
import Mathlib.Tactic

/-!
# Factorial finite-dimensional stationarity for the primary scalar path law

The aligned Wilson theorem already identifies the joint one-sided primary edge readout laws at a
finite set of nonnegative rational slots.  This file pushes that exact equality through the
canonical normalized-trace plaquette scalarization and, crucially, expresses the result directly on
the fixed scalar path carrier `ℚ → ℝ`.

For a finite slot set `J` and a nonnegative rational shift `t`, we use the continuous maps

`x ↦ (q ↦ x (q+t))` and `x ↦ (q ↦ x q)`,  `q : J`.

At every scale where `t` is exactly a natural number of lattice steps, their pushforward laws under
the actual finite scalar plaquette path measure agree.  The preceding factorial-subsequence theorem
then upgrades this to eventual exact equality along every primary-scalar Prokhorov subsequence at
canonical factorial spacing.

No continuum stationarity, adjacent-step regularity premise, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- Restriction of a scalar rational path to a fixed finite slot set after translating every slot by
`t`.  The codomain is the same fixed finite product `∀ q : J, ℝ`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
    (J : Finset ℚ)
    (t : ℚ) :
    C(ℚ → ℝ, ∀ q : J, ℝ) :=
  ⟨fun x q => x (q.1 + t), continuous_pi (fun q => continuous_apply (q.1 + t))⟩

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
        J t x q = x (q.1 + t) :=
  rfl

/-- On a nonnegative finite slot set, scalarizing the reflection-completed primary path and then
restricting to `J` agrees pointwise with scalarizing the actual finite primary readout. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestriction_reflectionCompleted_source
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
        J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A)) =
      (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            H latticeSpacing n J A q)) := by
  funext q
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A q.1) =
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          H latticeSpacing n A q.1)
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
      H latticeSpacing n A q.1 (hJ q)]

/-- If both the selected slots and the rational shift are nonnegative, the shifted scalar finite
restriction of the reflection-completed path is exactly the scalarization of the shifted actual
primary readout. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestriction_reflectionCompleted_source
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ)
    (ht : 0 ≤ t)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
        J t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A)) =
      (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
            H latticeSpacing n J t A q)) := by
  funext q
  have hqt : (0 : ℚ) ≤ q.1 + t := add_nonneg (hJ q) ht
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A (q.1 + t)) =
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          H latticeSpacing n A (q.1 + t))
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
      H latticeSpacing n A (q.1 + t) hqt]

local instance primaryScalarFactorialStationarityIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarFactorialStationarityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarFactorialStationaritySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarFactorialStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarFactorialStationarityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At every explicitly aligned nonnegative rational shift, the fixed finite-dimensional scalar
plaquette-coordinate law is exactly stationary under the actual finite scalar path measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_finiteRestriction_law_stationary_aligned
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (k : ℕ)
    (halign : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ)) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
          J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
          J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) := by
  let μ : Measure
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n
  let S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let Rt :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n J t
  let R0 :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n J
  let σ :=
    fun u :
        (∀ q : J,
          PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      fun q : J =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
          H N (u q)
  let τ : (ℚ → ℝ) → (∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
      J t
  let ρ : (ℚ → ℝ) → (∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap J
  have hX : Measurable X := by
    dsimp [X]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
        H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n
  have hS : Measurable S := by
    dsimp [S]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable H N
  have hRt : Measurable Rt := by
    dsimp [Rt]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_measurable
        H latticeSpacing n J t
  have hR0 : Measurable R0 := by
    dsimp [R0]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_measurable
        H latticeSpacing n J
  have hσ : Measurable σ := by
    dsimp [σ]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteFiniteSlotMap_measurable
        H N J
  have hτ : Measurable τ := by
    dsimp [τ]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
        J t).continuous.measurable
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
        J).continuous.measurable
  have hShiftSource : (τ ∘ S) ∘ X = σ ∘ Rt := by
    funext A
    simpa [τ, S, X, σ, Rt] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestriction_reflectionCompleted_source
        H N latticeSpacing n J hJ t ht A
  have hBaseSource : (ρ ∘ S) ∘ X = σ ∘ R0 := by
    funext A
    simpa [ρ, S, X, σ, R0] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestriction_reflectionCompleted_source
        H N latticeSpacing n J hJ A
  have hLaw : Measure.map Rt μ = Measure.map R0 μ := by
    dsimp [Rt, R0, μ]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_wilsonGibbs_law_stationary_aligned
        H N hN beta hbeta latticeSpacing latticeSpacing_pos n J hJ t k halign
  change
    Measure.map τ (Measure.map S (Measure.map X μ)) =
      Measure.map ρ (Measure.map S (Measure.map X μ))
  calc
    Measure.map τ (Measure.map S (Measure.map X μ)) =
        Measure.map (τ ∘ S) (Measure.map X μ) :=
      Measure.map_map hτ hS
    _ = Measure.map ((τ ∘ S) ∘ X) μ :=
      Measure.map_map (hτ.comp hS) hX
    _ = Measure.map (σ ∘ Rt) μ := by rw [hShiftSource]
    _ = Measure.map σ (Measure.map Rt μ) :=
      (Measure.map_map hσ hRt).symm
    _ = Measure.map σ (Measure.map R0 μ) :=
      congrArg (Measure.map σ) hLaw
    _ = Measure.map (σ ∘ R0) μ :=
      Measure.map_map hσ hR0
    _ = Measure.map ((ρ ∘ S) ∘ X) μ := by rw [hBaseSource]
    _ = Measure.map (ρ ∘ S) (Measure.map X μ) :=
      (Measure.map_map (hρ.comp hS) hX).symm
    _ = Measure.map ρ (Measure.map S (Measure.map X μ)) :=
      (Measure.map_map hρ hS).symm

/-- For canonical factorial spacing, every fixed nonnegative rational shift is eventually exactly
stationary on every fixed finite nonnegative scalar slot law along the chosen primary-scalar
Prokhorov subsequence. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_finiteRestriction_law_eventually_stationary
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t) :
    ∀ᶠ n : ℕ in atTop,
      Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
            J)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) := by
  filter_upwards [
    L.factorial_nonnegative_rational_eventually_naturalAligned H N hN beta hbeta t ht] with n hn
  rcases hn with ⟨k, hk⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_finiteRestriction_law_stationary_aligned
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (L.subsequence n) J hJ t ht k hk

end

end MathlibAnalytic
end MGAP4D
