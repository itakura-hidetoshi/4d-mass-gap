import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalReflectionCompletedAlignedMidpointCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalFactorialSubsequenceAlignment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquettePathLaw
import Mathlib.Tactic

/-!
# Aligned scalar OS midpoint pair laws at finite Wilson scale

The preceding coordinate layer identifies exactly the two reflection-completed path coordinates
that occur after translating a positive-time OS cylinder by an explicitly aligned nonnegative
rational shift `t`.

This file packages those two coordinates into a fixed finite-dimensional scalar carrier.  For a
finite nonnegative slot set `J`, compare

`q ↦ (x (-(q+t)), x (q+t))`

with

`q ↦ (x (-q), x ((q+t)+t))`.

At every finite Wilson scale where `t` is exactly `k` natural lattice steps, the two pair-valued
pushforward laws are equal under the actual same-root scalar path measure.  The proof uses only the
#1832 pointwise midpoint identities and exact integer temporal invariance of the same Wilson Gibbs
measure.  Canonical factorial spacing then makes this equality eventual along every primary-scalar
Prokhorov subsequence.

No whole-path translation invariance, continuum midpoint law, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- The symmetric pair of scalar coordinates used by the OS quadratic form after shifting every
positive slot by `t`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
    (J : Finset ℚ)
    (t : ℚ) :
    C(ℚ → ℝ, ∀ q : J, ℝ × ℝ) :=
  ⟨fun x q => (x (-(q.1 + t)), x (q.1 + t)),
    continuous_pi (fun q =>
      (continuous_apply (-(q.1 + t))).prod_mk (continuous_apply (q.1 + t)))⟩

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
        J t x q =
      (x (-(q.1 + t)), x (q.1 + t)) :=
  rfl

/-- The corresponding midpoint-resolved pair: the reflected member is returned to `-q`, while the
positive member advances to `q+2t`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
    (J : Finset ℚ)
    (t : ℚ) :
    C(ℚ → ℝ, ∀ q : J, ℝ × ℝ) :=
  ⟨fun x q => (x (-q.1), x ((q.1 + t) + t)),
    continuous_pi (fun q =>
      (continuous_apply (-q.1)).prod_mk (continuous_apply ((q.1 + t) + t)))⟩

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
        J t x q =
      (x (-q.1), x ((q.1 + t) + t)) :=
  rfl

local instance primaryScalarOSMidpointPairIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarOSMidpointPairCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarOSMidpointPairSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarOSMidpointPairMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarOSMidpointPairBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The #1832 edge-valued midpoint identities survive canonical plaquette scalarization exactly,
coordinatewise on every fixed finite nonnegative slot set. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPair_source_aligned
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (k : ℕ)
    (halign : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
        J t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n
            (periodicHypercubicIntegerTemporalConfigurationTranslation
              (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A))) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
        J t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A)) := by
  funext q
  apply Prod.ext
  · change
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n
            (periodicHypercubicIntegerTemporalConfigurationTranslation
              (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) (-(q.1 + t))) =
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A (-q.1))
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_neg_add_aligned_negConfigurationTranslation
        H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) ht k halign A]
  · change
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n
            (periodicHypercubicIntegerTemporalConfigurationTranslation
              (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) (q.1 + t)) =
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A ((q.1 + t) + t))
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_add_aligned_negConfigurationTranslation
        H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) ht k halign A]

/-- At every explicitly aligned nonnegative rational shift, the symmetric shifted OS coordinate pair
and its midpoint-resolved `(-q,q+2t)` pair have exactly the same law under the actual finite scalar
path measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_osMidpointPair_law_stationary_aligned
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
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
          J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
          J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := by
    refine ⟨?_⟩
    simp [PeriodicHypercubicEvenSideLength]
  let μ : Measure
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n
  let S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let T :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))
  let Pshift :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
      J t
  let Pbase :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
      J t
  have hX : Measurable X := by
    dsimp [X]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
        H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n
  have hS : Measurable S := by
    dsimp [S]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable H N
  have hT : Measurable T := by
    dsimp [T]
    exact
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))).measurable
  have hPshift : Measurable Pshift := by
    dsimp [Pshift]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
        J t).continuous.measurable
  have hPbase : Measurable Pbase := by
    dsimp [Pbase]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
        J t).continuous.measurable
  have hsource :
      (((Pshift : (ℚ → ℝ) → (∀ q : J, ℝ × ℝ)) ∘ S ∘ X) ∘ T) =
        ((Pbase : (ℚ → ℝ) → (∀ q : J, ℝ × ℝ)) ∘ S ∘ X) := by
    funext A
    simpa [Pshift, Pbase, S, X, T, Function.comp_apply] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPair_source_aligned
        H N latticeSpacing latticeSpacing_pos n J hJ t ht k halign A
  have hGibbs : Measure.map T μ = μ := by
    dsimp [T, μ]
    exact
      periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-(k : ℤ))
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
  change
    Measure.map Pshift (Measure.map S (Measure.map X μ)) =
      Measure.map Pbase (Measure.map S (Measure.map X μ))
  calc
    Measure.map Pshift (Measure.map S (Measure.map X μ)) =
        Measure.map (Pshift ∘ S) (Measure.map X μ) :=
      Measure.map_map hPshift hS
    _ = Measure.map ((Pshift ∘ S) ∘ X) μ :=
      Measure.map_map (hPshift.comp hS) hX
    _ = Measure.map ((Pshift ∘ S) ∘ X) (Measure.map T μ) := by
      rw [hGibbs]
    _ = Measure.map (((Pshift ∘ S) ∘ X) ∘ T) μ :=
      Measure.map_map ((hPshift.comp hS).comp hX) hT
    _ = Measure.map ((Pbase ∘ S) ∘ X) μ := by
      rw [hsource]
    _ = Measure.map (Pbase ∘ S) (Measure.map X μ) :=
      (Measure.map_map (hPbase.comp hS) hX).symm
    _ = Measure.map Pbase (Measure.map S (Measure.map X μ)) :=
      (Measure.map_map hPbase hS).symm

/-- Canonical factorial spacing turns the aligned finite midpoint-pair law into an eventual exact
identity along every primary-scalar Prokhorov subsequence. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_osMidpointPair_law_eventually_stationary
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
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointShiftedPairContinuousMap
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointBaseFuturePairContinuousMap
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) := by
  filter_upwards [
    L.factorial_nonnegative_rational_eventually_naturalAligned H N hN beta hbeta t ht] with n hn
  rcases hn with ⟨k, hk⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_osMidpointPair_law_stationary_aligned
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (L.subsequence n) J hJ t ht k hk

end

end MathlibAnalytic
end MGAP4D
