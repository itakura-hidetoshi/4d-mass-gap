import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Closed Hilbert realization of the actual finite-volume Gauss-law sector.

For every spatial lattice gauge transformation `γ`, take the kernel of
`U_γ - 1`, where `U_γ` is the Haar-`L²` pullback isometry constructed in the
preceding layer, and intersect these closed fixed-point subspaces.  This is the
same linear sector as the previously defined common fixed submodule, but now
closedness is part of the carrier itself. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
    (H N : ℕ) :
    ClosedSubmodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  ⨅ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
    (⊥ : ClosedSubmodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))).comap
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ).toContinuousLinearMap -
        ContinuousLinearMap.id ℝ
          (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

/-- Membership in the closed Gauss-law carrier is exactly invariance under all
actual spatial lattice gauge pullbacks. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_mem
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule H N ↔
      ∀ γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N,
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
          H N γ f = f := by
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule,
    sub_eq_zero]

/-- The closed carrier has exactly the same underlying linear subspace as the
Gauss-law fixed sector introduced in the gauge-action layer. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
      H N).toSubmodule =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  ext f
  simp

/-- Consequently the original Gauss-law invariant `L²` submodule is genuinely
closed in the complete Haar Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    (H N : ℕ) :
    IsClosed
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :
        Set (Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) := by
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq]
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
      H N).isClosed

/-- Orthogonal Gauss-law projection on the complete actual spatial-slice
Haar-`L²` Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection
    (H N : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
    H N).starProjection

/-- Every projected vector satisfies the finite-volume Gauss law. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f ∈
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq]
  exact Submodule.starProjection_apply_mem
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule H N) f

/-- The Gauss-law projection fixes exactly the gauge-invariant vectors. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f = f ↔
      f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  change
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
      H N).starProjection f = f ↔ _
  rw [Submodule.starProjection_eq_self_iff]
  simp

/-- The range of the orthogonal Gauss-law projection is precisely the physical
finite-volume fixed sector. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_range
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).range =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := by
  change
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule
      H N).starProjection).range = _
  rw [Submodule.range_starProjection]
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq
      H N

/-- Orthogonal projection is idempotent on the full Haar Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_idempotent
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).comp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N := by
  ext f
  exact
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
      H N _).2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N f)

/-- The component removed by Gauss-law projection is orthogonal to every
finite-volume physical vector. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlice_sub_GaussLawProjection_mem_orthogonal
    (H N : ℕ)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    f - periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f ∈
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)ᗮ := by
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule_toSubmodule_eq]
  exact Submodule.sub_starProjection_mem_orthogonal
    (K := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule H N)
    f

/-- Audit-visible receipt for the genuine finite-volume Gauss-law Hilbert
subspace and its orthogonal projector. -/
structure PeriodicHypercubicEvenSpecialUnitaryGaussLawProjectionPackage
    (H N : ℕ) : Prop where
  closed :
    IsClosed
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :
        Set (Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
  projectedPhysical :
    ∀ f,
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f ∈
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  fixedIff :
    ∀ f,
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f = f ↔
        f ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  rangeEq :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).range =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  idempotent :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).comp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N

/-- Construct the finite-volume Gauss-law Hilbert projection receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryGaussLawProjectionPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryGaussLawProjectionPackage H N :=
  { closed :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed H N
    projectedPhysical :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N
    fixedIff :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff H N
    rangeEq :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_range H N
    idempotent :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_idempotent H N }

end

end MathlibAnalytic
end MGAP4D
