import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryTransfer
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance canonicalBoundaryTransferGlobalNormSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryTransferGlobalNormSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryTransferGlobalNormSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryTransferGlobalNormSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryTransferGlobalNormSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryTransferGlobalNormSpecialUnitaryBorelSpace (N : ℕ) :
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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The canonical actual shared-boundary transfer has global operator norm
exactly one at every finite scale and every nonnegative time.

The upper bound is the structural contraction already proved for
`J_n T_{n,t/2} J_n†`.  The reverse bound is forced by the normalized boundary
vacuum, which this operator fixes exactly. -/
theorem canonicalBoundaryTransfer_opNorm_eq_one
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    ‖L.canonicalBoundaryTransfer C n t‖ = 1 := by
  letI : Nontrivial
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) := by
    refine ⟨⟨L.canonicalBoundaryVacuum n, 0, ?_⟩⟩
    intro hzero
    have hnorm := L.canonicalBoundaryVacuum_norm n
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  apply le_antisymm
  · exact L.canonicalBoundaryTransfer_opNorm_le C n t
  · have h :=
      (L.canonicalBoundaryTransfer C n t).le_opNorm
        (L.canonicalBoundaryVacuum n)
    rw [L.canonicalBoundaryTransfer_fixes_vacuum,
      L.canonicalBoundaryVacuum_norm] at h
    simpa using h

/-- Consequently, no scalar strictly below one can be a global operator-norm
upper bound for the canonical boundary transfer.  Any strict finite-volume gap
estimate must therefore remove the vacuum direction (equivalently, work on a
vacuum-orthogonal/centered compression) rather than contract the full boundary
`L²` operator. -/
theorem canonicalBoundaryTransfer_no_strict_global_opNorm_bound
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) {r : ℝ}
    (hr : r < 1) :
    ¬ ‖L.canonicalBoundaryTransfer C n t‖ ≤ r := by
  rw [L.canonicalBoundaryTransfer_opNorm_eq_one C n t]
  exact not_le_of_gt hr

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end