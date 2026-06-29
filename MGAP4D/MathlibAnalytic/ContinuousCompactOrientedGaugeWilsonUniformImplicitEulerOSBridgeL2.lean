import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerFamilyL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExcitationFiniteVolumeGapTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

/-- Scalar-norm convergence data connecting the uniformly gapped compact
Wilson implicit-Euler excitation spaces to one continuum OS physical
semigroup.  The finite Hilbert carriers may vary with scale. -/
structure ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ) where
  approximate :
    (n : ℕ) → P.VacuumOrthogonalHilbert →L[ℝ]
      (U.system n).VacuumOrthogonalL2
  approximate_norm_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto
        (fun n : ℕ => ‖approximate n psi‖)
        atTop
        (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n : ℕ =>
          ‖U.uniformImplicitEulerL2 n t (approximate n psi)‖)
        atTop
        (nhds
          ‖T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert)‖)

namespace ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ}

/-- The compact Wilson implicit-Euler bridge instantiates the abstract
excitation-only finite-volume OS gap transfer package. -/
noncomputable def toExcitationFiniteVolumeGapTransfer
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U) :
    T.ExcitationFiniteVolumeGapTransfer where
  mass := continuousCompactOrientedUniformDobrushinGap U
  mass_pos := continuous_compact_oriented_uniformDobrushinGap_pos U
  decayFactor := implicitEulerGapDecayFactor
    (continuousCompactOrientedUniformDobrushinGap U)
  slope_tendsto :=
    continuous_compact_oriented_uniformImplicitEulerL2_decay_slope U
  FiniteExcitation := fun n => (U.system n).VacuumOrthogonalL2
  finiteNormedAddCommGroup := fun _ => inferInstance
  finiteInnerProductSpace := fun _ => inferInstance
  finiteOperator := fun n t => U.uniformImplicitEulerL2 n t
  approximate := B.approximate
  approximate_norm_tendsto := B.approximate_norm_tendsto
  evolved_norm_tendsto := B.evolved_norm_tendsto
  finite_decay := by
    intro n t phi
    exact
      continuous_compact_oriented_uniformImplicitEulerL2_norm_bound
        U n t phi

/-- The uniform compact Wilson bridge produces a continuum vacuum-sector gap
slope with mass exactly `1 - coefficientBound`. -/
noncomputable def toVacuumSemigroupGapSlope
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U) :
    T.VacuumSemigroupGapSlope :=
  B.toExcitationFiniteVolumeGapTransfer.toVacuumSemigroupGapSlope

/-- The resulting continuum right Hamiltonian has the uniform Dobrushin
Rayleigh lower bound on its vacuum-orthogonal generator domain. -/
theorem rightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedUniformDobrushinGap U *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    B.toExcitationFiniteVolumeGapTransfer
      |>.rightHamiltonian_inner_ge_mass_mul_norm_sq T psi hpsi

/-- The same uniform lower bound survives graph closure of the continuum OS
Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedUniformDobrushinGap U *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T B.toVacuumSemigroupGapSlope hP psi hpsi

end ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge

end

end MathlibAnalytic
end MGAP4D
