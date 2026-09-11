import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopEigenvector
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Replace exactly one actual spatial-slice link by a new `SU(N)` value.

This is deliberately defined on the intrinsic spatial-slice carrier.  No
identification with the full four-dimensional Wilson configuration carrier is
used or assumed. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N := by
  classical
  exact Function.update A target g

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink_self
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink H N A target g target = g := by
  classical
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink]

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink_of_ne
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (he : e ≠ target) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink H N A target g e = A e := by
  classical
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink, he]

/-- The physical ground-state vacuum amplitude seen along one actual spatial
link fiber.

For a fixed boundary configuration `A` and link `target`, this is

`g ↦ Ω(A[target ← g])`.

The canonical physical `Ω` is only an `L²` representative, so `ofReal` keeps
this definition total without silently promoting almost-everywhere
nonnegativity to pointwise nonnegativity.  In the later Wilson-Doob
application, positivity and two-sided distortion bounds must therefore be
proved on the concrete fiber rather than inferred from the global `L²` class. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
      (periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink
        H N A target g))

/-- Normalize an arbitrary raw one-link probability law by the actual physical
vacuum amplitude on the corresponding spatial-link fiber.

The raw law is kept explicit here.  A later model-specific theorem may identify
it with a literal Wilson one-link conditional law; this layer does not assume
such a carrier identification. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoobMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target)

/-- Exact local information required to control the Doob distortion caused by
the physical vacuum on one spatial-link fiber.

The important point is that these are genuinely fiberwise hypotheses.  The
existing global statement `Ω > 0` almost everywhere does not by itself provide
a positive pointwise lower bound on every fiber. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberDistortionData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) where
  m : ℝ≥0∞
  M : ℝ≥0∞
  measurable :
    AEMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target) nu
  lower_pos : 0 < m
  upper_finite : M < ∞
  lower : ∀ g,
    m ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target g
  upper : ∀ g,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
        H N hN beta hbeta A target g ≤ M

/-- Sharp one-link variance transfer from a raw spatial-link probability law to
the physical ground-state Doob law.

Once a concrete Wilson one-link conditional law is identified with `nu`, the
only remaining analytic input is the local vacuum oscillation receipt `D`.
The loss is exactly the density ratio `D.m / D.M`; no lattice-volume factor is
introduced in this step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoob_evariance_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    [IsProbabilityMeasure nu]
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberDistortionData
        H N hN beta hbeta nu A target)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2 nu) :
    (D.m / D.M) * evariance X nu ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoobMeasure
          H N hN beta hbeta nu A target) := by
  exact doobWeightedMeasure_evariance_lower_bound
    nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target)
    X D.m D.M D.measurable D.lower_pos D.upper_finite D.lower D.upper hX

end

end MathlibAnalytic
end MGAP4D
