import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathContinuumReflectionInvariance
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Same-root rational positive-cylinder reflection forms and their continuum limit

The authoritative same-root rational path law is already constructed from the
actual finite Wilson Gibbs measures, and its full rational-path law is already
proved invariant under Euclidean time reflection.  The next OS step needs more
than invariance: it needs a positive-time cylinder algebra whose quadratic
reflection forms can be identified with the finite Wilson Gram forms and then
passed to the continuum.

This file closes the topology/weak-convergence part of that step without adding
a reflection-positivity premise.

* A positive rational cylinder is a bounded continuous function of finitely many
  nonnegative rational time coordinates.
* Its pullback to the rational path carrier is a Mathlib
  `BoundedContinuousFunction`.
* Its real OS reflection integrand `F(θx) * F(x)` is again bounded continuous.
* Factorial alignment makes the reflected finite path observable eventually
  agree exactly with the actual finite configuration reflection.
* Mathlib weak convergence of probability measures then gives convergence of
  these same-root finite reflection forms to the continuum reflection form.

What remains deliberately open after this file is the model-facing positive-half
factorization: identify the eventually aligned finite positive-time cylinder
pullback with an admissible bounded-continuous positive-half Wilson observable.
Once that identification is supplied, the existing finite Wilson OS/Gram theorem
provides nonnegativity, and the limit theorem below transports it to the same-root
continuum law.

No continuum reflection positivity axiom, Hilbert reconstruction, spectral
assumption, exact mass value, or additional physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory ProbabilityTheory

noncomputable section

local instance rationalPositiveCylinderNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rationalPositiveCylinderTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance rationalPositiveCylinderCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance rationalPositiveCylinderSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance rationalPositiveCylinderMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance rationalPositiveCylinderBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A bounded continuous cylinder observable supported at finitely many
nonnegative rational Euclidean times.  Repeated time labels are allowed. -/
structure PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder where
  slotCount : ℕ
  time : Fin slotCount → ℚ
  time_nonneg : ∀ i, 0 ≤ time i
  observable : BoundedContinuousFunction (Fin slotCount → ℝ) ℝ

/-- The labelled finite rational-coordinate readout as a continuous map from the
full rational path carrier. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReadoutContinuousMap
    (m : ℕ) (time : Fin m → ℚ) :
    C(ℚ → ℝ, Fin m → ℝ) :=
  ⟨(fun x i => x (time i)), continuous_pi (fun i => continuous_apply (time i))⟩

/-- Euclidean time reflection packaged as a Mathlib continuous map. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflectionContinuousMap :
    C(ℚ → ℝ, ℚ → ℝ) :=
  ⟨periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_continuous⟩

/-- Pull a finite positive rational cylinder back to the complete rational path
carrier. -/
noncomputable def
    PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.pathObservable
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  Cyl.observable.compContinuous
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReadoutContinuousMap
      Cyl.slotCount Cyl.time)

@[simp]
theorem
    PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.pathObservable_apply
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder)
    (x : ℚ → ℝ) :
    Cyl.pathObservable x = Cyl.observable (fun i => x (Cyl.time i)) :=
  rfl

/-- The real Osterwalder--Schrader quadratic integrand `F(θx) F(x)` associated
with a positive rational cylinder.  Bounded continuity is generated by Mathlib
composition and pointwise multiplication. -/
noncomputable def
    PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.realReflectionIntegrand
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  (Cyl.pathObservable.compContinuous
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflectionContinuousMap) *
    Cyl.pathObservable

@[simp]
theorem
    PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.realReflectionIntegrand_apply
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder)
    (x : ℚ → ℝ) :
    Cyl.realReflectionIntegrand x =
      Cyl.pathObservable
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection x) *
        Cyl.pathObservable x :=
  rfl

/-- The real OS quadratic reflection form of a positive rational cylinder against
an arbitrary measure on the rational path carrier. -/
noncomputable def
    PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.realReflectionForm
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder)
    (μ : Measure (ℚ → ℝ)) : ℝ :=
  ∫ x, Cyl.realReflectionIntegrand x ∂μ

/-- Along the canonical factorial Prokhorov subsequence, every time slot of a
fixed positive rational cylinder is eventually an exact lattice multiple. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_positiveCylinder_eventually_latticeMultiple
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin Cyl.slotCount,
        ∃ k : ℤ,
          (Cyl.time i : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n) := by
  exact
    L.subsequence_strictMono.tendsto_atTop.eventually
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_eventually_latticeMultiple
        Cyl.slotCount Cyl.time)

/-- For every fixed positive rational cylinder, factorial alignment makes path
reflection agree eventually and pointwise with the actual finite Wilson
configuration reflection.  This is the exact geometric identity needed before
identifying the finite quadratic form with the finite Wilson OS/Gram form. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_positiveCylinder_configurationReflection_eventually
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    ∀ᶠ n : ℕ in atTop,
      ∀ A : PeriodicHypercubicEvenEdge (H (L.subsequence n)) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        Cyl.pathObservable
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence n)
              (periodicHypercubicEvenConfigurationReflection (H (L.subsequence n)) A)) =
          Cyl.pathObservable
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection
              (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
                (H (L.subsequence n)) N hN
                (beta (L.subsequence n)) (hbeta (L.subsequence n))
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n) A)) := by
  have hCov :=
    L.subsequence_strictMono.tendsto_atTop.eventually
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_finRational_configurationReflection_eventually
        H N hN beta hbeta Cyl.slotCount Cyl.time)
  filter_upwards [hCov] with n hn
  intro A
  simpa [
      PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.pathObservable,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReadoutContinuousMap,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection] using
    congrArg Cyl.observable (hn A)

/-- Consequently, the finite same-root path reflection integrand is eventually
literally the product of the positive cylinder observable on the reflected and
unreflected actual Wilson configurations. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_positiveCylinder_reflectionIntegrand_readout_eventually
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    ∀ᶠ n : ℕ in atTop,
      ∀ A : PeriodicHypercubicEvenEdge (H (L.subsequence n)) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        Cyl.realReflectionIntegrand
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence n) A) =
          Cyl.pathObservable
              (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
                (H (L.subsequence n)) N hN
                (beta (L.subsequence n)) (hbeta (L.subsequence n))
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n)
                (periodicHypercubicEvenConfigurationReflection (H (L.subsequence n)) A)) *
            Cyl.pathObservable
              (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
                (H (L.subsequence n)) N hN
                (beta (L.subsequence n)) (hbeta (L.subsequence n))
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n) A) := by
  filter_upwards [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_positiveCylinder_configurationReflection_eventually
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L Cyl] with n hn
  intro A
  rw [PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.realReflectionIntegrand_apply]
  rw [← hn A]

/-- Mathlib weak convergence transfers every fixed bounded-continuous positive
rational-cylinder reflection form from the actual same-root finite Wilson path
laws to the Prokhorov continuum law.

This proves the convergence part of continuum OS reflection positivity.  No
finite or continuum nonnegativity hypothesis is used here. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_positiveCylinder_reflectionForm_tendsto_continuum
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (Cyl : PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder) :
    Tendsto
      (fun n : ℕ =>
        Cyl.realReflectionForm
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n) : Measure (ℚ → ℝ)))
      atTop
      (nhds
        (Cyl.realReflectionForm
          (show Measure (ℚ → ℝ) from
            (L.continuumMeasure : Measure
              (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
                H N hN beta hbeta
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
                physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.PhysicalConfiguration)))) := by
  have hIntegral :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      L.weakConvergence) Cyl.realReflectionIntegrand
  simpa [
      PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPositiveCylinder.realReflectionForm,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq] using
    hIntegral

end

end MathlibAnalytic
end MGAP4D
