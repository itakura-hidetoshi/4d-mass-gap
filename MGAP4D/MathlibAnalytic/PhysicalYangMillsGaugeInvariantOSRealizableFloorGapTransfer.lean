import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAsymptoticFiniteVolumeMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscretePhysicalContraction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsFloorExponentialTransferTrajectory
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableFloorGapTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableFloorGapTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableFloorGapTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableFloorGapTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableFloorGapTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableFloorGapTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact norm factor at the canonical realizable floor-selected physical time
`k_n a_n`, with `k_n = floor (t / a_n)`. -/
def physicalYangMillsExact3320FloorNormFactor
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (t : NNReal) (n : ℕ) : ℝ :=
  Real.exp
    (-physicalYangMillsExact3320Mass *
      ((physicalTemporalFloorNatStep S.latticeSpacing t n : ℝ) *
        S.latticeSpacing n))

/-- The floor-selected exact factor is definitionally the geometric power of
the actual one-lattice-step factor. -/
theorem physicalYangMillsExact3320FloorNormFactor_eq_pow
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (t : NNReal) (n : ℕ) :
    physicalYangMillsExact3320FloorNormFactor S t n =
      (physicalYangMillsExact3320OneStepNormFactor S n) ^
        physicalTemporalFloorNatStep S.latticeSpacing t n := by
  unfold physicalYangMillsExact3320FloorNormFactor
    physicalYangMillsExact3320OneStepNormFactor
  symm
  change
    Real.exp (-physicalYangMillsExact3320Mass * S.latticeSpacing n) ^
        physicalTemporalFloorNatStep S.latticeSpacing t n =
      Real.exp
        (-physicalYangMillsExact3320Mass *
          ((physicalTemporalFloorNatStep S.latticeSpacing t n : ℝ) *
            S.latticeSpacing n))
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The exact floor-selected finite norm factors converge to the exact
continuum factor `exp (-(33/20) t)`. -/
theorem physicalYangMillsExact3320FloorNormFactor_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (t : NNReal) :
    Tendsto
      (fun n : ℕ => physicalYangMillsExact3320FloorNormFactor S t n)
      atTop
      (nhds (Real.exp (-physicalYangMillsExact3320Mass * (t : ℝ)))) := by
  simpa only [physicalYangMillsExact3320FloorNormFactor] using
    physicalTemporalFloorExponentialFactor_tendsto
      S.latticeSpacing S.latticeSpacing_pos S.latticeSpacing_tendsto_zero
      physicalYangMillsExact3320Mass t

/-- Common-carrier convergence bridge for the genuinely discrete finite Wilson
OS evolution.

For each continuum target time `t`, the finite operator is evaluated only at
the realizable lattice time selected by `floor (t / a_n)`.  The structure does
not postulate an all-real-time finite semigroup.  Its only dynamical convergence
input is convergence of these selected evolved vectors to the continuum OS
semigroup orbit. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) where
  approximate :
    (n : ℕ) → P.PhysicalHilbert →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert
  embed :
    (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert
        →L[ℝ] P.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ)
      (phi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert),
      ‖embed n phi‖ = ‖phi‖
  approximate_orthogonal :
    ∀ (n : ℕ) (psi : P.PhysicalHilbert),
      inner ℝ psi P.vacuum = 0 →
        inner ℝ (approximate n psi)
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuum = 0
  approximate_tendsto :
    ∀ psi : P.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n psi))
        atTop
        (nhds psi)
  evolved_floor_tendsto :
    ∀ (t : NNReal) (psi : P.PhysicalHilbert),
      Tendsto
        (fun n : ℕ =>
          embed n
            (G.realizablePhysicalOperator n
              (physicalTemporalFloorNatStep S.latticeSpacing t n)
              (approximate n psi)))
        atTop
        (nhds (T.toPhysicalSemigroup.operator t psi))

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer

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
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant}

/-- The actual completed finite Wilson operator at the floor-selected time obeys
the exact floor-selected exponential bound on the vacuum-orthogonal sector. -/
theorem finite_floor_operator_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G)
    (n : ℕ) (t : NNReal)
    (phi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
    (hphi : inner ℝ phi
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuum = 0) :
    ‖G.realizablePhysicalOperator n
        (physicalTemporalFloorNatStep S.latticeSpacing t n) phi‖ ≤
      physicalYangMillsExact3320FloorNormFactor S t n * ‖phi‖ := by
  have h := G.realizablePhysicalOperator_vacuumOrthogonal_norm_le_pow
    n (physicalTemporalFloorNatStep S.latticeSpacing t n) phi hphi
  simpa only [physicalYangMillsExact3320FloorNormFactor_eq_pow] using h

/-- Install the actual discrete Wilson floor trajectory into the generic
scale-dependent common-carrier gap transfer. -/
noncomputable def toEmbeddedAsymptoticFiniteVolumeVacuumGapTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G) :
    T.EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer where
  mass := physicalYangMillsExact3320Mass
  mass_pos := physicalYangMillsExact3320Mass_pos
  decayFactor := fun t =>
    Real.exp (-physicalYangMillsExact3320Mass * (t : ℝ))
  slope_tendsto :=
    tendsto_nnreal_inv_mul_one_sub_exp_neg_mul physicalYangMillsExact3320Mass
  FiniteState := fun n =>
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert
  finiteNormedAddCommGroup := fun _ => inferInstance
  finiteInnerProductSpace := fun _ => inferInstance
  finiteVacuum := fun n =>
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuum
  finiteOperator := fun n t =>
    G.realizablePhysicalOperator n
      (physicalTemporalFloorNatStep S.latticeSpacing t n)
  finiteDecayFactor := fun n t =>
    physicalYangMillsExact3320FloorNormFactor S t n
  finiteDecayFactor_tendsto := fun t =>
    physicalYangMillsExact3320FloorNormFactor_tendsto S t
  approximate := A.approximate
  embed := A.embed
  embed_norm := A.embed_norm
  approximate_orthogonal := A.approximate_orthogonal
  approximate_tendsto := A.approximate_tendsto
  evolved_tendsto := A.evolved_floor_tendsto
  finite_decay := by
    intro n t phi hphi
    exact A.finite_floor_operator_norm_le n t phi hphi

/-- The floor-selected actual finite Wilson trajectory generates exact
continuum vacuum-sector exponential decay with mass `33/20`. -/
noncomputable def toVacuumSemigroupGapSlope
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G) :
    T.VacuumSemigroupGapSlope :=
  A.toEmbeddedAsymptoticFiniteVolumeVacuumGapTransfer.toVacuumSemigroupGapSlope

/-- Exact continuum semigroup decay produced by the realizable discrete Wilson
floor trajectory. -/
theorem continuum_operator_vacuumOrthogonal_norm_le_exp_3320
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (hpsi : inner ℝ psi P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      Real.exp (-physicalYangMillsExact3320Mass * (t : ℝ)) * ‖psi‖ := by
  exact A.toVacuumSemigroupGapSlope.decay t psi hpsi

/-- The realizable discrete Wilson floor trajectory yields the exact `33/20`
Rayleigh lower bound on the continuum right-Hamiltonian generator domain. -/
theorem rightHamiltonian_inner_ge_3320_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (33 : ℝ) / 20 * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  simpa [physicalYangMillsExact3320Mass] using
    A.toEmbeddedAsymptoticFiniteVolumeVacuumGapTransfer
      |>.rightHamiltonian_inner_ge_mass_mul_norm_sq T psi hpsi

/-- The same exact `33/20` lower bound survives graph closure of the continuum
OS Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_3320_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant P T G)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (33 : ℝ) / 20 * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  simpa [physicalYangMillsExact3320Mass] using
    A.toEmbeddedAsymptoticFiniteVolumeVacuumGapTransfer
      |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq T hP psi hpsi

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
