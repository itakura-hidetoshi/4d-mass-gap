import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalReflectionCompletedAlignedMidpointCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalFactorialSubsequenceAlignment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquettePathLaw
import Mathlib.Tactic

/-!
# Factorial finite OS midpoint pair law on the primary scalar path

The preceding finite geometry isolates exactly the two reflection-completed coordinates needed by a
translated OS quadratic form.  This file scalarizes those coordinates and packages them in the fixed
carrier

`(∀ q : J, ℝ) × (∀ q : J, ℝ)`.

For `q ≥ 0`, the translated symmetric pair is

`(x (-(q+t)), x (q+t))`,

while the midpoint pair is

`(x (-q), x ((q+t)+t))`.

At every finite Wilson scale where `t` is aligned with `k` natural lattice steps, translating the
underlying source by `-k` sends the translated pair exactly to the midpoint pair.  Invariance of the
actual Wilson Gibbs law under that source translation therefore gives exact equality of the two
fixed scalar pair laws.  Canonical factorial spacing then makes this equality eventual along every
primary-scalar Prokhorov subsequence.

No continuum midpoint identity, OS contraction, null-space preservation, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- The symmetric pair of scalar finite restrictions occurring in the OS quadratic form after a
positive rational shift `t`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
    (J : Finset ℚ)
    (t : ℚ) :
    C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) := by
  refine ⟨fun x =>
    ((fun q : J => x (-(q.1 + t))),
      fun q : J => x (q.1 + t)), ?_⟩
  exact
    (continuous_pi (fun q : J => continuous_apply (-(q.1 + t)))).prod_mk
      (continuous_pi (fun q : J => continuous_apply (q.1 + t)))

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap_fst_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t x).1 q = x (-(q.1 + t)) :=
  rfl

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap_snd_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t x).2 q = x (q.1 + t) :=
  rfl

/-- The midpoint pair obtained after using source-translation invariance on the shifted OS pair. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
    (J : Finset ℚ)
    (t : ℚ) :
    C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) := by
  refine ⟨fun x =>
    ((fun q : J => x (-q.1)),
      fun q : J => x ((q.1 + t) + t)), ?_⟩
  exact
    (continuous_pi (fun q : J => continuous_apply (-q.1))).prod_mk
      (continuous_pi (fun q : J => continuous_apply ((q.1 + t) + t)))

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap_fst_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
      J t x).1 q = x (-q.1) :=
  rfl

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap_snd_apply
    (J : Finset ℚ)
    (t : ℚ)
    (x : ℚ → ℝ)
    (q : J) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
      J t x).2 q = x ((q.1 + t) + t) :=
  rfl

/-- Scalarized pointwise source identity behind the finite OS midpoint law.  Only the symmetric
coordinates `±(q+t)` are translated; no global path covariance is asserted. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPair_sourceTranslation_eq_midpoint
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (k : ℕ)
    (halign : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
        J t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n
            (periodicHypercubicIntegerTemporalConfigurationTranslation
              (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A))) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
        J t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A)) := by
  apply Prod.ext
  · funext q
    exact congrArg
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_neg_add_aligned_negConfigurationTranslation
        H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) ht k halign A)
  · funext q
    exact congrArg
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_add_aligned_negConfigurationTranslation
        H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) ht k halign A)

local instance primaryScalarOSMidpointPairTopologicalGroup (N : ℕ) :
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

/-- At an explicitly aligned finite scale, the translated OS symmetric scalar pair law equals the
midpoint pair law exactly under the actual finite scalar path measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_osShiftedPair_law_eq_midpoint_aligned
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
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
          J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
          J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let μ : Measure
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n
  let S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let Y := S ∘ X
  let T :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))
  let P :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t
  let Q :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
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
  have hY : Measurable Y := hS.comp hX
  have hT : Measurable T := by
    dsimp [T]
    exact
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))).measurable
  have hP : Measurable P := by
    dsimp [P]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
        J t).continuous.measurable
  have hQ : Measurable Q := by
    dsimp [Q]
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
        J t).continuous.measurable
  have hTlaw : Measure.map T μ = μ := by
    dsimp [T, μ]
    exact
      periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-(k : ℤ))
  have hsource : (P ∘ Y) ∘ T = Q ∘ Y := by
    funext A
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPair_sourceTranslation_eq_midpoint
        H N latticeSpacing latticeSpacing_pos n J hJ t ht k halign A
  change
    Measure.map P (Measure.map S (Measure.map X μ)) =
      Measure.map Q (Measure.map S (Measure.map X μ))
  calc
    Measure.map P (Measure.map S (Measure.map X μ)) =
        Measure.map P (Measure.map Y μ) := by
      congr 1
      exact Measure.map_map hS hX
    _ = Measure.map P (Measure.map Y (Measure.map T μ)) := by
      rw [hTlaw]
    _ = Measure.map (P ∘ Y) (Measure.map T μ) :=
      Measure.map_map hP hY
    _ = Measure.map ((P ∘ Y) ∘ T) μ :=
      Measure.map_map (hP.comp hY) hT
    _ = Measure.map (Q ∘ Y) μ := by rw [hsource]
    _ = Measure.map Q (Measure.map Y μ) :=
      (Measure.map_map hQ hY).symm
    _ = Measure.map Q (Measure.map S (Measure.map X μ)) := by
      congr 1
      exact (Measure.map_map hS hX).symm

/-- At canonical factorial spacing, every fixed finite nonnegative slot set and nonnegative rational
shift has eventual exact OS midpoint pair-law equality along the selected primary-scalar Prokhorov
subsequence. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_osShiftedPair_law_eventually_eq_midpoint
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
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
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
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_osShiftedPair_law_eq_midpoint_aligned
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (L.subsequence n) J hJ t ht k hk

end

end MathlibAnalytic
end MGAP4D
