import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUniformQ0RangeRawKernelBridge
import Mathlib.Tactic

/-!
# Explicit boundary formula for the centered SU(N) two-mode finite OS states

This layer removes the finite-OS Hilbert centering operation from the remaining
H1-D range obligation.

A real linear isometry preserves vacuum centering exactly.  Combining this
generic fact with the #5003 pointwise coherent boundary readout rewrites the
boundary image of every concrete centered finite OS state as

  finiteVacuumCentered (J_n Omega_n) f_{k,n},

where `f_{k,n}` is the explicit primary-plaquette SU(N) Haar two-mode boundary
vector.

Thus the remaining one-sided range statement becomes a purely boundary-Haar
statement.  No identification of the OS vacuum line with the full normalized
transfer top eigenspace is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance sunTwoModeCenteredBoundaryFormulaTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeCenteredBoundaryFormulaCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeCenteredBoundaryFormulaSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeCenteredBoundaryFormulaMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeCenteredBoundaryFormulaBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real linear isometries preserve vacuum centering exactly. -/
theorem linearIsometry_finiteVacuumCentered
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J : E →ₗᵢ[ℝ] F)
    (vacuum x : E) :
    J (finiteVacuumCentered vacuum x) =
      finiteVacuumCentered (J vacuum) (J x) := by
  unfold finiteVacuumCentered
  rw [map_sub, map_smul, J.inner_map_map]

section SUNTwoModeCenteredBoundaryFormula

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant}

/-- Exact boundary-Haar formula for the concrete #5003 centered finite OS
state.  The only vacuum vector appearing on the right is the exact image
`J_n Omega_n`; no top-sector identification is inserted. -/
theorem physicalYangMillsSUNTwoModeCenteredFiniteOSState_boundaryMoment_eq
    (k : Fin 2) (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
    J (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n) =
      finiteVacuumCentered
        (J Pn.vacuum)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          (halfExtent n) hN2 k) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  change
    J
        (finiteVacuumCentered Pn.vacuum
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap (P.observable k)))) =
      finiteVacuumCentered
        (J Pn.vacuum)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          (halfExtent n) hN2 k)
  rw [linearIsometry_finiteVacuumCentered]
  rw [P.boundaryMoment_eq_primaryPlaquetteWilsonTwoModeBoundaryHaarL2]

/-- Pure boundary-Haar form of the residual H1-D one-sided range statement. -/
def PhysicalYangMillsSUNTwoModeExplicitCenteredBoundaryOneSidedExcitationRange :
    Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
    finiteVacuumCentered
        (J Pn.vacuum)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          (halfExtent n) hN2 k) ∈
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        (halfExtent n) N hN (beta n) (hbeta n)

/-- The #5007 range obligation is exactly the explicit boundary-Haar
membership statement above.  This is an iff, so no compatibility information is
lost in the reduction. -/
theorem physicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange_iff_explicit
    :
    PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange
        (P := P) ↔
      PhysicalYangMillsSUNTwoModeExplicitCenteredBoundaryOneSidedExcitationRange
        (Q := Q) (hInvariant := hInvariant) := by
  constructor
  · intro h k n
    have hk := h k n
    rw [physicalYangMillsSUNTwoModeCenteredFiniteOSState_boundaryMoment_eq] at hk
    exact hk
  · intro h k n
    have hk := h k n
    rw [physicalYangMillsSUNTwoModeCenteredFiniteOSState_boundaryMoment_eq]
    exact hk

end SUNTwoModeCenteredBoundaryFormula

end

end MathlibAnalytic
end MGAP4D
