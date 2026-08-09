import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalProjectiveL2Carrier
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

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

/-- Selected finite-marginal realization by the **actual periodic-even compact
`SU(N)` Wilson Gibbs source**.

The surrounding projective cylinder family already carries projective
consistency.  This structure records only the model-specific statement needed
at each Wilson scale used by the OS carrier:

* one finite projective marginal is an actual pushforward of that scale's
  compact Wilson Gibbs law;
* a measurable readout of the observed finite coordinates recovers the actual
  reflection-fixed boundary configuration pointwise.

The boundary marginal law is deliberately *not* stored.  It is generated below
from this commuting observation diagram and the existing theorem identifying
the exact pushforward of the compact Wilson Gibbs law under boundary
restriction. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  observe :
    (n : ℕ) →
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (∀ x : marginalIndex n, F.fieldValue x)
  observe_measurable : ∀ n, Measurable (observe n)
  finiteMarginal_eq_map_wilsonGibbs :
    ∀ n,
      F.finiteMarginal (marginalIndex n) =
        Measure.map (observe n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure
  boundaryReadout :
    (n : ℕ) →
      (∀ x : marginalIndex n, F.fieldValue x) →
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
          (halfExtent n) N
  boundaryReadout_measurable : ∀ n, Measurable (boundaryReadout n)
  boundaryReadout_observe :
    ∀ n
      (A : PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ),
      boundaryReadout n (observe n A) =
        (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).boundaryRestriction A

namespace PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery

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

/-- The actual interacting boundary marginal is theorem-generated from the
compact-Wilson/projective commuting diagram.

The proof is only functoriality of `Measure.map`, pointwise equality of the two
boundary observations, and the already-proved compact Wilson boundary
pushforward theorem.  In particular no boundary-law equality remains as an
independent model input. -/
theorem map_finiteMarginal_eq_boundaryMarginal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery
      Q F)
    (n : ℕ) :
    Measure.map (R.boundaryReadout n)
        (F.finiteMarginal (R.marginalIndex n)) =
      periodicHypercubicEvenBoundaryMarginalMeasure
        (halfExtent n) N hN (beta n) (hbeta n) := by
  rw [R.finiteMarginal_eq_map_wilsonGibbs n]
  let μ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).gibbsMeasure
  calc
    Measure.map (R.boundaryReadout n)
        (Measure.map (R.observe n) μ) =
      Measure.map (R.boundaryReadout n ∘ R.observe n) μ := by
        exact Measure.map_map
          (R.boundaryReadout_measurable n)
          (R.observe_measurable n)
    _ = Measure.map
        (periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).boundaryRestriction μ := by
      congr 1
      funext A
      exact R.boundaryReadout_observe n A
    _ = periodicHypercubicEvenBoundaryMarginalMeasure
        (halfExtent n) N hN (beta n) (hbeta n) := by
      exact
        periodicHypercubicEvenSpecialUnitary_map_boundaryRestriction_gibbsMeasure
          (halfExtent n) N hN (beta n) (hbeta n)

/-- Forget the compact Wilson source realization and recover exactly the
interacting-boundary projective readout interface introduced in #1584.

Its previously opaque marginal-law field is now filled by the theorem above. -/
noncomputable def toBoundaryMarginalProjectiveReadout
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery
      Q F) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F where
  marginalIndex := R.marginalIndex
  boundaryReadout := R.boundaryReadout
  boundaryReadout_measurable := R.boundaryReadout_measurable
  map_finiteMarginal_eq_boundaryMarginal :=
    R.map_finiteMarginal_eq_boundaryMarginal

/-- Consequently the complete density-corrected finite OS-to-projective
isometry is generated from the actual compact Wilson observation diagram. -/
noncomputable def finiteOSMarginalLinearIsometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.toBoundaryMarginalProjectiveReadout).finiteOSMarginalLinearIsometry
    hInvariant n

@[simp] theorem finiteOSMarginalLinearIsometry_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖R.finiteOSMarginalLinearIsometry hInvariant n phi‖ = ‖phi‖ :=
  (R.finiteOSMarginalLinearIsometry hInvariant n).norm_map phi

end PhysicalYangMillsEvenPeriodicWilsonOSCompactProjectiveBoundaryRecovery

end

end MathlibAnalytic
end MGAP4D
