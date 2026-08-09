import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepDerivedRateGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingCenteredQuadraticLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumHalfQuadraticGapClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumVacuum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSUniformVarianceContinuumExcitation
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableFloorWeakStarDerivedRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableFloorWeakStarDerivedRateSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableFloorWeakStarDerivedRateSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableFloorWeakStarDerivedRateSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableFloorWeakStarDerivedRateSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableFloorWeakStarDerivedRateSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Scalar weak-star floor transfer for a continuum rate derived from the
actual finite one-step factors.

There are no maps between changing finite Hilbert spaces and the continuum
Hilbert space. Finite time remains genuinely `ℕ`-indexed. The only dynamical
limit field is convergence of the evolved centered scalar OS quadratic value
along floor-selected lattice times. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
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
    (transferFactor : ℕ → ℝ)
    (A : PositiveDiscreteTransferRateLimit S.latticeSpacing transferFactor)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (T :
      let Pinf :=
        physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
      Pinf.PositiveTimeObservableContractionSemigroup) where
  exchange : T.ReflectionTimeTranslationExchange
  evolved_floor_centered_quadratic_tendsto :
    ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
      let Pinf :=
        physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
      Tendsto
        (fun n : ℕ =>
          let Pn :=
            physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          Pn.osQuadraticValue
            (R.realizableCarrierTranslation hInvariant n
              (physicalTemporalFloorNatStep S.latticeSpacing (t / 2) n)
              (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F))))
        atTop
        (nhds
          (Pinf.osQuadraticValue
            (T.carrierTranslation (t / 2)
              (Pinf.vacuumCenteredCarrier (Pinf.carrierOfPositiveTime F)))))

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer

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
    {transferFactor : ℕ → ℝ}
    {A : PositiveDiscreteTransferRateLimit S.latticeSpacing transferFactor}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor}
    {T :
      let Pinf :=
        physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
      Pinf.PositiveTimeObservableContractionSemigroup}

/-- The actual integer-time one-step estimate gives the floor-selected
half-time quadratic estimate with the scale-dependent factor extracted from the
finite transfer dynamics. -/
theorem finite_floor_half_quadratic_le
    (W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T)
    (n : ℕ) (t : NNReal) (F : D.positiveTimeSubalgebra) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.osQuadraticValue
        (R.realizableCarrierTranslation hInvariant n
          (physicalTemporalFloorNatStep S.latticeSpacing (t / 2) n)
          (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F))) ≤
      A.floorHalfQuadraticFactor t n *
        Pn.osQuadraticValue
          (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime F)) := by
  dsimp only
  have h := G.centered_osQuadraticValue_le_pow_sq
    n (physicalTemporalFloorNatStep S.latticeSpacing (t / 2) n)
    ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).carrierOfPositiveTime F)
  dsimp only at h
  unfold PositiveDiscreteTransferRateLimit.floorHalfQuadraticFactor
  rw [A.floorFactor_eq_pow]
  exact h

/-- Scalar weak-star convergence transports the finite rate limit into an
actual continuum half-quadratic gap certificate. Its mass is the limit of
`-log(rₙ)/aₙ`, not a preselected constant. -/
noncomputable def toHalfQuadraticGapCertificate
    (W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T) :
    T.HalfQuadraticGapCertificate where
  mass := A.mass
  mass_pos := A.mass_pos
  quadraticDecayFactor := fun t =>
    Real.exp (-A.mass * (t : ℝ))
  quadraticDecayFactor_nonneg :=
    exponential_quadraticDecayFactor_nonneg A.mass
  slope_tendsto :=
    exponential_quadraticDecayFactor_slope_tendsto A.mass
  exchange := W.exchange
  core_half_quadratic_decay := by
    intro t F
    let Pinf :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
    let Fpos := Pinf.positiveTimeElement F
    have hleft := W.evolved_floor_centered_quadratic_tendsto t Fpos
    have hinitial :=
      physical_yang_mills_evenPeriodicWilsonOS_centeredQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant Fpos
    have hfactor := A.floorHalfQuadraticFactor_tendsto t
    have hright := hfactor.mul hinitial
    have hfinite : ∀ n : ℕ,
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        Pn.osQuadraticValue
            (R.realizableCarrierTranslation hInvariant n
              (physicalTemporalFloorNatStep S.latticeSpacing (t / 2) n)
              (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos))) ≤
          A.floorHalfQuadraticFactor t n *
            Pn.osQuadraticValue
              (Pn.vacuumCenteredCarrier (Pn.carrierOfPositiveTime Fpos)) := by
      intro n
      exact W.finite_floor_half_quadratic_le n t Fpos
    have hlimit := le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall hfinite)
    simpa only [Fpos, Pinf.carrierOfPositiveTime_positiveTimeElement] using hlimit

/-- The actual continuum Wilson OS vacuum normalization remains
weak-star-theorem-generated; it is not a field of the transfer package. -/
theorem continuum_isNormalized
    (_W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T) :
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant).IsNormalized :=
  physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant

/-- The derived rate gives the continuum vacuum-orthogonal semigroup norm
decay with no common finite/continuum Hilbert-space embeddings. -/
theorem continuum_operator_vacuumOrthogonal_norm_le_exp
    (W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T)
    (t : NNReal)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant).PhysicalHilbert)
    (hpsi : inner ℝ psi
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant).vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      Real.exp (-A.mass * (t : ℝ)) * ‖psi‖ := by
  have h := W.toHalfQuadraticGapCertificate.norm_decay
    W.continuum_isNormalized t psi hpsi
  change
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      Real.sqrt
        (Real.exp (-A.mass * (((t + t : NNReal) : ℝ)))) * ‖psi‖ at h
  simpa only [sqrt_exp_neg_mul_double_nnreal] using h

/-- A finite uniform variance certificate supplies the nonzero continuum
excitation needed to compare the derived rate with the variational mass of the
actual graph-closed OS Hamiltonian. -/
theorem mass_le_physicalYangMillsMass_of_uniformCenteredVariance
    (W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T)
    {F : D.positiveTimeSubalgebra}
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant F)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    let Ts :=
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous
    A.mass ≤ Ts.physicalYangMillsMass := by
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant
  let Ts : Pinf.StronglyContinuousPhysicalSemigroup :=
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous
  let H := W.toHalfQuadraticGapCertificate
  let hP : Pinf.IsNormalized := W.continuum_isNormalized
  have hSelf : IsSelfAdjoint Ts.closedRightHamiltonian := by
    simpa only [Ts] using H.closedRightHamiltonian_isSelfAdjoint hContinuous
  let phi : Pinf.VacuumOrthogonalHilbert := V.continuumExcitation
  have hphi : phi ≠ 0 := by
    simpa only [phi] using V.continuumExcitation_ne_zero
  let X : Ts.PhysicalYangMillsExcitationDomainWitness :=
    Ts.physicalYangMillsExcitationDomainWitness_of_nonzeroExcitation
      hP hSelf phi hphi
  apply Ts.uniformRayleighLowerBound_le_physicalYangMillsMass X
  intro psi _hpsi horthogonal
  simpa only [H, Ts, Pinf] using
    H.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      hP hContinuous psi horthogonal

/-- Consequently a positive limiting logarithmic rate extracted from actual
finite transfer factors proves positivity of the physical Yang--Mills mass,
once one fixed Wilson observable has a non-collapsing centered variance. -/
theorem physicalYangMillsMass_pos_of_uniformCenteredVariance
    (W : PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor A G T)
    {F : D.positiveTimeSubalgebra}
    (V : PhysicalYangMillsEvenPeriodicWilsonOSUniformCenteredVarianceCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant F)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    let Ts :=
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous
    0 < Ts.physicalYangMillsMass := by
  have hLower := W.mass_le_physicalYangMillsMass_of_uniformCenteredVariance
    V hContinuous
  exact lt_of_lt_of_le A.mass_pos hLower

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableFloorWeakStarDerivedRateGapTransfer

end MathlibAnalytic
end MGAP4D

end
