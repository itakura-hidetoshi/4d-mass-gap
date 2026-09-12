import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalReflectionCompletedPathLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import Mathlib.Tactic
import Mathlib.Tactic.FunProp

/-!
# Canonical scalar plaquette path law from the completed primary rational path

The reflection-completed edge-valued rational path law is finite-scale because
its spatial-boundary edge carrier depends on the half extent `H`.  For the
continuum route we now pass, without identifying edge carriers across scales,
to the fixed scalar carrier `ℚ → ℝ`.

The scalar coordinate is not arbitrary: at each rational time it is the
normalized real trace of the canonical primary spatial plaquette, assembled
from exactly its four one-sided primary spatial boundary edges in the existing
orientation `a b c⁻¹ d⁻¹`.

This file constructs the scalarization, proves measurability and exact
commutation with rational path reflection, and pushes the already-constructed
finite completed path law to `ℚ → ℝ`.  No cross-scale equality, continuum
premise, positivity premise, closedness premise, or new physical assumption is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The `k`-th physical edge of the canonical primary spatial plaquette,
packaged directly in the one-sided primary spatial boundary carrier. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge
    (H : ℕ) (k : Fin 4) :
    PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H :=
  ⟨periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k,
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k,
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k⟩

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge_val
    (H : ℕ) (k : Fin 4) :
    (periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge H k).1 =
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k := by
  rfl

/-- Canonical scalar Wilson coordinate on a one-sided primary spatial boundary
configuration.  It is written as `1 - E_W` so continuity is inherited directly
from the existing Wilson-energy theorem; the next theorem identifies it with
the normalized real trace. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
    (H N : ℕ)
    (u : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  1 - specialUnitaryWilsonPlaquetteEnergy N
    (orientedFourEdgePlaquetteWord
      (fun k =>
        u (periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge H k)))

/-- The scalar coordinate is exactly the normalized real trace of the canonical
orientation-correct four-edge plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_eq
    (H N : ℕ)
    (u : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N u =
      normalizedSpecialUnitaryRealTrace N
        (orientedFourEdgePlaquetteWord
          (fun k =>
            u (periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge H k))) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  ring

/-- Same-root readback on an actual finite configuration: restricting to the
one-sided primary spatial edge carrier and applying the scalar coordinate gives
exactly the normalized trace of the actual canonical primary plaquette
holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_restrict_eq_actual
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (fun e => A e.1) =
      normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_eq]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge]
  rfl

local instance primaryScalarPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Continuity of the canonical scalar primary-boundary plaquette coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_continuous
    (H N : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N) := by
  have hword :
      Continuous
        (fun u : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          orientedFourEdgePlaquetteWord
            (fun k =>
              u (periodicHypercubicEvenPrimarySpatialPlaquettePrimaryBoundaryEdge H k))) := by
    unfold orientedFourEdgePlaquetteWord
    fun_prop
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
  exact continuous_const.sub
    ((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hword)

/-- Measurability of the canonical scalar primary-boundary plaquette coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N) :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_continuous
    H N).measurable

/-- Coordinatewise scalarization of the reflection-completed edge-valued
rational path.  Its codomain `ℚ → ℝ` no longer depends on `H`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
    (H N : ℕ)
    (x : ℚ →
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ℚ → ℝ :=
  fun q =>
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
      H N (x q)

/-- The scalarization map into the fixed rational real path carrier is
measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N) := by
  apply measurable_pi_lambda
  intro q
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_measurable
      H N).comp (measurable_pi_apply q)

/-- Reflection on the fixed scalar rational path carrier. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
    (x : ℚ → ℝ) :
    ℚ → ℝ :=
  fun q => x (-q)

/-- Scalar rational path reflection is measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable :
    Measurable
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply (-q)

/-- Scalarization commutes exactly with the intrinsic rational path reflection. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_reflection
    (H N : ℕ)
    (x : ℚ →
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H x) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N x) := by
  rfl

/-- The finite scalar rational path law, obtained by pushing the actual
reflection-completed primary path law to the fixed carrier `ℚ → ℝ`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure (ℚ → ℝ) :=
  Measure.map
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N)
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
      H N hN beta hbeta latticeSpacing n)

/-- Probability-measure packaging of the same fixed-carrier scalar rational path
law. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    ProbabilityMeasure (ℚ → ℝ) :=
  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathProbabilityMeasure
    H N hN beta hbeta latticeSpacing n).map
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
        H N).aemeasurable

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n := by
  rfl

/-- Audit-visible same-root identity: the scalar law is exactly the pushforward
of the completed primary path law, with no cross-scale carrier identification. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_eq_map_completedPath
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
          H N hN beta hbeta latticeSpacing n) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
