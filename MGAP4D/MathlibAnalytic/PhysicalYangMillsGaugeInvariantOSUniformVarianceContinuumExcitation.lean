import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingCenteredQuadraticLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredQuadraticExcitation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

/-- A quantitative nontriviality certificate for one fixed positive-time
Wilson/OS observable along the actual even-periodic finite-volume
approximation.

The certificate deliberately contains no proposed mass value.  Its only
quantitative datum is a strictly positive lower floor for the centered OS
quadratic value of one observable at every finite scale. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (F : D.positiveTimeSubalgebra) where
  varianceFloor : ℝ
  varianceFloor_pos : 0 < varianceFloor
  finite_centered_quadratic_ge :
    ∀ n : ℕ,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      varianceFloor ≤
        Pn.osQuadraticValue
          (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F))

namespace PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate

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
    {F : D.positiveTimeSubalgebra}

/-- The scale-uniform finite Wilson variance floor survives weak-star passage to
the actual continuum OS state.

This is the precise no-collapse statement needed for excitation-sector
nontriviality. -/
theorem continuum_centered_quadratic_ge
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F) :
    let Pinf :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    V.varianceFloor ≤
      Pinf.osQuadraticValue
        (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F)) := by
  let finiteValue : ℕ → ℝ := fun n =>
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    Pn.osQuadraticValue
      (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F))
  let continuumValue : ℝ :=
    let Pinf :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    Pinf.osQuadraticValue
      (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F))
  have hfinite : ∀ n : ℕ, V.varianceFloor ≤ finiteValue n := by
    intro n
    simpa only [finiteValue] using V.finite_centered_quadratic_ge n
  have hlimit : Tendsto finiteValue atTop (nhds continuumValue) := by
    simpa only [finiteValue, continuumValue] using
      physical_yang_mills_evenPeriodicWilsonOS_centeredQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta B hInvariant F
  have hle : V.varianceFloor ≤ continuumValue := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
    exact Filter.Eventually.of_forall hfinite
  simpa only [continuumValue] using hle

/-- Hence the actual continuum centered OS quadratic value is strictly
positive. -/
theorem continuum_centered_quadratic_pos
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F) :
    let Pinf :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    0 <
      Pinf.osQuadraticValue
        (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F)) := by
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  have hge :
      V.varianceFloor ≤
        Pinf.osQuadraticValue
          (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F)) := by
    simpa only [Pinf] using V.continuum_centered_quadratic_ge
  exact lt_of_lt_of_le V.varianceFloor_pos hge

/-- The fixed Wilson observable therefore produces an actual vector of the
continuum OS vacuum-orthogonal Hilbert sector. -/
noncomputable def continuumExcitation
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F) :
    let Pinf :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    Pinf.VacuumOrthogonalHilbert := by
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  exact
    Pinf.centeredPhysicalExcitation
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta B hInvariant)
      (Pinf.carrierOfPositiveTime F)

/-- The continuum excitation generated by the finite uniform variance
certificate is genuinely nonzero. -/
theorem continuumExcitation_ne_zero
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F) :
    V.continuumExcitation ≠ 0 := by
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  let hP : Pinf.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta B hInvariant
  have hpos :
      0 < Pinf.osQuadraticValue
        (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F)) := by
    simpa only [Pinf] using V.continuum_centered_quadratic_pos
  simpa only [continuumExcitation, Pinf, hP] using
    Pinf.centeredPhysicalExcitation_ne_zero_of_osQuadraticValue_pos
      hP (Pinf.carrierOfPositiveTime F) hpos

/-- In particular the actual continuum OS excitation Hilbert space contains two
distinct vectors.  This is a theorem-generated consequence of a finite Wilson
variance floor, not an independent Hilbert-space assumption. -/
theorem continuumVacuumOrthogonalHilbert_nontrivial
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta B hInvariant F) :
    ∃ phi :
        (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant).VacuumOrthogonalHilbert,
      phi ≠ 0 := by
  exact ⟨V.continuumExcitation, V.continuumExcitation_ne_zero⟩

end PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate

end

end MathlibAnalytic
end MGAP4D
