import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.RealLinearIsometrySeparationCompletionRange

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryImageClosureSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryImageClosureSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryImageClosureSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryImageClosureSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryImageClosureSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryImageClosureSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The actual completed finite Wilson OS boundary image is precisely the
Hilbert closure of the theorem-generated canonical Wilson boundary moments.

In symbols,

`range Ĵ_n = closure { m_n(F) | F in the OS carrier }`.

Thus Hilbert completion introduces no ambient boundary states beyond limits of
actual canonical Wilson moments, and no surjectivity onto the full boundary
`L²` space is asserted or needed. -/
theorem range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_canonicalBoundaryMoment
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) =
      closure (Set.range (fun F :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F)) := by
  rw [physicalHilbertBoundaryMomentLinearIsometry]
  simpa only [Q.boundaryMomentLinearIsometry_apply] using
    (range_realLinearIsometrySeparationCompletion_eq_closure_range
      (Q.boundaryMomentLinearIsometry hInvariant n))

/-- Membership in the physical OS boundary image is therefore exactly a
closure condition for canonical Wilson moments.  This is the formulation
needed to replace exact-observable realization by a density argument. -/
theorem mem_range_physicalHilbertBoundaryMomentLinearIsometry_iff_mem_closure_canonicalBoundaryMoment
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    x ∈ Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n) ↔
      x ∈ closure (Set.range (fun F :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F)) := by
  rw [Q.range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_canonicalBoundaryMoment]

/-- The actual completed Wilson OS boundary image is closed in boundary Haar
`L²`, as expected for the image of a complete Hilbert space under a linear
isometry. -/
theorem isClosed_range_physicalHilbertBoundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    IsClosed (Set.range (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)) := by
  rw [Q.range_physicalHilbertBoundaryMomentLinearIsometry_eq_closure_canonicalBoundaryMoment]
  exact isClosed_closure

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end
