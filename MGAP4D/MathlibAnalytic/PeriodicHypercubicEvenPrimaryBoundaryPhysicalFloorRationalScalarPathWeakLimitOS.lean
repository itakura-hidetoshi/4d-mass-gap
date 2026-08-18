import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathIntrinsicOS
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Order.OrderClosed

/-!
# Weak-limit OS positivity for the one-sided primary scalar rational path

The finite scalar rational path law is already constructed on the fixed carrier
`ℚ → ℝ`, and its intrinsic Osterwalder--Schrader quadratic form is nonnegative
for every bounded measurable cylinder whose finite nonnegative rational slots
are physically admissible at that lattice scale.

This file isolates the fixed-carrier weak-limit step.  A positive cylinder is a
bounded continuous function of a finite `Finset ℚ` of nonnegative rational
slots.  Its path observable and reflected quadratic integrand are bounded
continuous.  Therefore Mathlib weak convergence of probability measures gives
convergence of the reflection forms.  If the explicit finite-slot admissibility
condition holds eventually, the finite theorem supplies eventual nonnegativity,
and closedness of `[0,∞)` transfers that nonnegativity to the weak limit.

Crucially, eventual admissibility is an explicit hypothesis here.  It is not
inferred from physical-volume growth, no identity such as `physicalVolume = H*a`
is introduced, and no full-boundary-vacuum positive-locality statement is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory ProbabilityTheory

noncomputable section

local instance primaryScalarWeakLimitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarWeakLimitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarWeakLimitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarWeakLimitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarWeakLimitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A bounded continuous cylinder supported on a finite set of nonnegative
rational Euclidean times, aligned exactly with the `Finset` carrier used by the
finite one-sided primary OS theorem. -/
structure PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder where
  slots : Finset ℚ
  slots_nonneg : ∀ q ∈ slots, 0 ≤ q
  observable : BoundedContinuousFunction (∀ q : slots, ℝ) ℝ

/-- Finite slot restriction as a continuous map on the fixed rational path
carrier. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
    (J : Finset ℚ) :
    C(ℚ → ℝ, ∀ q : J, ℝ) :=
  ⟨fun x q => x q.1, continuous_pi (fun q => continuous_apply q.1)⟩

/-- Pull a positive scalar cylinder back to the complete rational path carrier. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.pathObservable
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  Cyl.observable.compContinuous
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
      Cyl.slots)

@[simp]
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.pathObservable_apply
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (x : ℚ → ℝ) :
    Cyl.pathObservable x = Cyl.observable (fun q : Cyl.slots => x q.1) :=
  rfl

/-- Intrinsic scalar rational path reflection packaged as a continuous map. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflectionContinuousMap :
    C(ℚ → ℝ, ℚ → ℝ) :=
  ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection,
    continuous_pi (fun q => continuous_apply (-q))⟩

/-- The bounded-continuous intrinsic OS quadratic integrand `F(x) F(Θx)`. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionIntegrand
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  Cyl.pathObservable *
    Cyl.pathObservable.compContinuous
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflectionContinuousMap

@[simp]
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionIntegrand_apply
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (x : ℚ → ℝ) :
    Cyl.realReflectionIntegrand x =
      Cyl.pathObservable x *
        Cyl.pathObservable
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) :=
  rfl

/-- The intrinsic real OS reflection form against an arbitrary measure on the
fixed scalar rational path carrier. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionForm
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (μ : Measure (ℚ → ℝ)) : ℝ :=
  ∫ x, Cyl.realReflectionIntegrand x ∂μ

/-- At every scale where the cylinder slots satisfy the explicit one-sided
primary physical-floor admissibility condition, the actual finite scalar path
law has a nonnegative intrinsic OS reflection form. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_finiteReflectionForm_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n Cyl.slots) :
    0 ≤ Cyl.realReflectionForm
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ)) := by
  have hfinite :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_intrinsicReflectionPositive_boundedMeasurable
      H N hN beta hbeta latticeSpacing n Cyl.slots hslots
      Cyl.observable Cyl.observable.continuous.measurable
      ‖Cyl.observable‖ (norm_nonneg _) (fun v => Cyl.observable.norm_coe_le_norm v)
  simpa [
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionForm,
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionIntegrand_apply,
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.pathObservable_apply,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction]
    using hfinite

/-- Weak convergence on the fixed carrier transfers every bounded-continuous
primary scalar reflection form.  This theorem is purely topological and uses no
finite positivity assumption. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_reflectionForm_tendsto_of_weakConvergence
    (μ : ℕ → ProbabilityMeasure (ℚ → ℝ))
    (μlim : ProbabilityMeasure (ℚ → ℝ))
    (hweak : Tendsto μ atTop (nhds μlim))
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    Tendsto
      (fun n => Cyl.realReflectionForm (μ n : Measure (ℚ → ℝ)))
      atTop
      (nhds (Cyl.realReflectionForm (μlim : Measure (ℚ → ℝ)))) := by
  have hIntegral :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
      Cyl.realReflectionIntegrand
  simpa [
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionForm]
    using hIntegral

/-- Main weak-limit bridge for the new one-sided primary scalar law.

If the actual finite scalar path laws converge weakly on `ℚ → ℝ` and the
finite set of nonnegative cylinder slots is explicitly admissible eventually,
then the limiting path law has a nonnegative intrinsic OS reflection form for
that cylinder.

No conclusion about eventual slot admissibility is extracted from a volume
limit here; it must be supplied by the chosen scaling geometry. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_weakLimit_reflectionForm_nonneg
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (μlim : ProbabilityMeasure (ℚ → ℝ))
    (hweak :
      Tendsto
        (fun n =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H n) N hN (beta n) (hbeta n) latticeSpacing n)
        atTop
        (nhds μlim))
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (hslots :
      ∀ᶠ n : ℕ in atTop,
        PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
          (H n) latticeSpacing n Cyl.slots) :
    0 ≤ Cyl.realReflectionForm (μlim : Measure (ℚ → ℝ)) := by
  have hforms :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_reflectionForm_tendsto_of_weakConvergence
      (fun n =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H n) N hN (beta n) (hbeta n) latticeSpacing n)
      μlim hweak Cyl
  have hfinite :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ Cyl.realReflectionForm
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H n) N hN (beta n) (hbeta n) latticeSpacing n : Measure (ℚ → ℝ)) := by
    filter_upwards [hslots] with n hn
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_finiteReflectionForm_nonneg
        (H n) N hN (beta n) (hbeta n) latticeSpacing n Cyl hn
  exact isClosed_Ici.mem_of_tendsto hforms hfinite

end

end MathlibAnalytic
end MGAP4D
