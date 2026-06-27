import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHalfQuadraticGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteVolumeMassGapTransfer
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- A continuum vacuum-sector gap stated on the dense centered observable core
through half-time OS quadratic values.

This is the natural continuum endpoint of a finite Wilson reflected-integral
estimate. -/
structure HalfQuadraticGapCertificate
    (T : P.PositiveTimeObservableContractionSemigroup) where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : T.ReflectionTimeTranslationExchange
  core_half_quadratic_decay :
    ∀ (t : NNReal) (F : P.Carrier),
      P.osQuadraticValue
          (T.carrierTranslation (t / 2) (P.vacuumCenteredCarrier F)) ≤
        quadraticDecayFactor t *
          P.osQuadraticValue (P.vacuumCenteredCarrier F)

namespace HalfQuadraticGapCertificate

variable {T : P.PositiveTimeObservableContractionSemigroup}

/-- The half-time OS estimate implies a diagonal quadratic estimate for every
vector in the completed vacuum-orthogonal Hilbert sector. -/
theorem quadratic_decay
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (t : NNReal)
    (phi : P.PhysicalHilbert)
    (hphi : inner ℝ phi P.vacuum = 0) :
    inner ℝ (T.toPhysicalSemigroup.operator t phi) phi ≤
      Q.quadraticDecayFactor t * ‖phi‖ ^ 2 := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup.quadratic_decay_of_observable_core
      T.toPhysicalSemigroup hP (Q.quadraticDecayFactor t) t
      (by
        intro F
        let Fc := P.vacuumCenteredCarrier F
        have hcenter :
            P.physicalState Fc =
              finiteVacuumCentered P.vacuum (P.physicalState F) :=
          P.physicalState_vacuumCenteredCarrier F
        calc
          inner ℝ
              (T.toPhysicalSemigroup.operator t
                (finiteVacuumCentered P.vacuum (P.physicalState F)))
              (finiteVacuumCentered P.vacuum (P.physicalState F)) =
            D.osBilinForm P.omega
              (P.toPositiveTime (T.carrierTranslation t Fc))
              (P.toPositiveTime Fc) := by
            rw [← hcenter]
            exact T.inner_operator_physicalState_eq_osBilinForm t Fc
          _ = P.osQuadraticValue (T.carrierTranslation (t / 2) Fc) :=
            T.osBilinForm_carrierTranslation_eq_osQuadraticValue_half
              Q.exchange t Fc
          _ ≤ Q.quadraticDecayFactor t * P.osQuadraticValue Fc :=
            Q.core_half_quadratic_decay t F
          _ = Q.quadraticDecayFactor t *
              ‖finiteVacuumCentered P.vacuum (P.physicalState F)‖ ^ 2 := by
            rw [← hcenter, P.norm_physicalState,
              P.osQuadraticValue_eq_norm_sq])
      phi hphi

/-- The diagonal quadratic estimate and semigroup square identity yield the
completed continuum transfer-operator norm decay. -/
theorem norm_decay
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (t : NNReal)
    (phi : P.PhysicalHilbert)
    (hphi : inner ℝ phi P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t phi‖ ≤
      Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖ := by
  have hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric :=
    Q.exchange.toPhysicalSemigroup_isInnerSymmetric
  have hsq :
      ‖T.toPhysicalSemigroup.operator t phi‖ ^ 2 ≤
        Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 := by
    calc
      ‖T.toPhysicalSemigroup.operator t phi‖ ^ 2 =
          inner ℝ (T.toPhysicalSemigroup.operator (t + t) phi) phi :=
        T.toPhysicalSemigroup.operator_norm_sq_eq_inner_operator_add_self
          hSymmetric t phi
      _ ≤ Q.quadraticDecayFactor (t + t) * ‖phi‖ ^ 2 :=
        Q.quadratic_decay hP (t + t) phi hphi
  have hq : 0 ≤ Q.quadraticDecayFactor (t + t) :=
    Q.quadraticDecayFactor_nonneg (t + t)
  have hsqrt_sq :
      (Real.sqrt (Q.quadraticDecayFactor (t + t))) ^ 2 =
        Q.quadraticDecayFactor (t + t) :=
    Real.sq_sqrt hq
  have hleft : 0 ≤ ‖T.toPhysicalSemigroup.operator t phi‖ := norm_nonneg _
  have hright :
      0 ≤ Real.sqrt (Q.quadraticDecayFactor (t + t)) * ‖phi‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

/-- A continuum half-time OS quadratic certificate produces the semigroup gap
slope consumed by the right-Hamiltonian mass-gap theorem. -/
noncomputable def toVacuumSemigroupGapSlope
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous).VacuumSemigroupGapSlope where
  mass := Q.mass
  mass_pos := Q.mass_pos
  decayFactor := fun t =>
    Real.sqrt (Q.quadraticDecayFactor (t + t))
  slope_tendsto := Q.slope_tendsto
  decay := by
    intro t phi hphi
    simpa only [StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup_toPhysicalSemigroup]
      using Q.norm_decay hP t phi hphi

/-- Hence the continuum right Hamiltonian has Rayleigh quotient at least the
positive mass on its vacuum-orthogonal generator domain. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (Q : T.HalfQuadraticGapCertificate)
    (hP : P.IsNormalized)
    (hContinuous : T.StrongContinuityOnObservableStates)
    (psi : (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
      T hContinuous).rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ
        ((StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
          T hContinuous).rightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous)
      (Q.toVacuumSemigroupGapSlope hP hContinuous)
      psi hpsi

end HalfQuadraticGapCertificate
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
