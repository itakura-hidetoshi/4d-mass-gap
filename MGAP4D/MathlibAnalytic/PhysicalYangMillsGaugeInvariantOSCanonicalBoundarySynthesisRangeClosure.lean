import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualAdjointSynthesisBoundaryTransferGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance canonicalBoundarySynthesisRangeSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundarySynthesisRangeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundarySynthesisRangeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundarySynthesisRangeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundarySynthesisRangeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundarySynthesisRangeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Every vector in the completed physical boundary realization belongs to the
closure of the range of the *actual* Wilson adjoint-synthesis operator
`A_φ†`.

On the dense raw OS carrier this is exact, because each canonical boundary
moment is literally `A_φ† u_F`.  Completion then only closes that actual
synthesis range; no abstract feature operator or gap hypothesis is used. -/
theorem completedLinearIsometry_mem_closure_actualBoundarySynthesis_range
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    L.completedLinearIsometry n psi ∈
      closure (Set.range
        (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n)) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  change UniformSpace.Completion Pn.Separated at psi
  refine UniformSpace.Completion.induction_on psi
    (isClosed_closure.preimage (L.completedLinearMap n).continuous) ?_
  intro x
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  change L.completedLinearMap n
      ((SeparationQuotient.mk F : Pn.Separated) :
        UniformSpace.Completion Pn.Separated) ∈ _
  rw [L.completedLinearMap_coe, L.separatedLinearIsometry_mk]
  apply subset_closure
  refine ⟨physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
    S D halfExtent N hN beta hbeta B hInvariant n F, ?_⟩
  exact
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta B hInvariant n F).symm

/-- The canonical shared-boundary transfer never leaves the closure of the
actual Wilson adjoint-synthesis range.

Since `K_{n,t} = J_n T_{n,t/2} J_n†`, every output is in the completed physical
boundary image, and the previous theorem places that image inside
`closure (range A_φ†)`. -/
theorem canonicalBoundaryTransfer_mem_closure_actualBoundarySynthesis_range
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    L.canonicalBoundaryTransfer C n t v ∈
      closure (Set.range
        (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n)) := by
  change
    L.completedLinearMap n
      (C.finiteOperator n (t / 2)
        ((((L.completedLinearIsometry n).toContinuousLinearMap)†) v)) ∈ _
  exact L.completedLinearIsometry_mem_closure_actualBoundarySynthesis_range n _

/-- Operator-range form of the same statement.  The remaining exact
analysis-factor problem is therefore not a question of whether the physical
boundary transfer points toward the Wilson synthesis space: it already lands
in its closure.  What remains is the quantitative bounded lifting from this
closed physical image through `A_φ†`. -/
theorem canonicalBoundaryTransfer_range_subset_closure_actualBoundarySynthesis_range
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    Set.range (L.canonicalBoundaryTransfer C n t) ⊆
      closure (Set.range
        (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n)) := by
  rintro w ⟨v, rfl⟩
  exact L.canonicalBoundaryTransfer_mem_closure_actualBoundarySynthesis_range
    C n t v

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end
