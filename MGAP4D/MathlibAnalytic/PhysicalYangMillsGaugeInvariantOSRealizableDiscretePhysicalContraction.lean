import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAdditiveContractionAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320Gap
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableDiscretePhysicalContractionSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableDiscretePhysicalContractionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableDiscretePhysicalContractionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableDiscretePhysicalContractionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableDiscretePhysicalContractionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableDiscretePhysicalContractionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

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

/-- The exact centered one-step estimate implies nonexpansiveness of every
realizable discrete carrier translation on the whole OS seminormed carrier.
Vacuum and excitation components are compared through the normalized Hilbert
Pythagorean identity, so no separate global contraction assumption is needed. -/
theorem realizableCarrierTranslation_norm_le
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖R.realizableCarrierTranslation hInvariant n k F‖ ≤ ‖F‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let r := physicalYangMillsExact3320OneStepNormFactor S n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hr0 : 0 ≤ r :=
    (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
  have hr1 : r ≤ 1 :=
    physicalYangMillsExact3320OneStepNormFactor_le_one S n
  have hrpow : r ^ k ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        exact mul_le_mul ih hr1 (pow_nonneg hr0 k) zero_le_one
  have hcenter := G.centered_norm_le_pow n k F
  dsimp only at hcenter
  have hcenterContract :
      ‖R.realizableCarrierTranslation hInvariant n k
          (Pn.vacuumCenteredCarrier F)‖ ≤
        ‖Pn.vacuumCenteredCarrier F‖ := by
    calc
      ‖R.realizableCarrierTranslation hInvariant n k
          (Pn.vacuumCenteredCarrier F)‖ ≤
        r ^ k * ‖Pn.vacuumCenteredCarrier F‖ := hcenter
      _ ≤ 1 * ‖Pn.vacuumCenteredCarrier F‖ :=
        mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
      _ = ‖Pn.vacuumCenteredCarrier F‖ := one_mul _
  have hcomm :=
    R.realizableCarrierTranslation_vacuumCenteredCarrier hInvariant n k F
  dsimp only at hcomm
  have hcenterTranslated :
      ‖Pn.vacuumCenteredCarrier
          (R.realizableCarrierTranslation hInvariant n k F)‖ ≤
        ‖Pn.vacuumCenteredCarrier F‖ := by
    rw [← hcomm]
    exact hcenterContract
  have hcenterSq :
      ‖Pn.vacuumCenteredCarrier
          (R.realizableCarrierTranslation hInvariant n k F)‖ ^ 2 ≤
        ‖Pn.vacuumCenteredCarrier F‖ ^ 2 := by
    nlinarith [
      norm_nonneg
        (Pn.vacuumCenteredCarrier
          (R.realizableCarrierTranslation hInvariant n k F)),
      norm_nonneg (Pn.vacuumCenteredCarrier F)]
  have hsqOut := Pn.vacuumCenteredCarrier_norm_sq hPn
    (R.realizableCarrierTranslation hInvariant n k F)
  have hsqIn := Pn.vacuumCenteredCarrier_norm_sq hPn F
  have homega := R.realizableCarrierTranslation_omega hInvariant n k F
  dsimp only at homega
  rw [hsqOut, hsqIn, homega] at hcenterSq
  nlinarith [
    norm_nonneg (R.realizableCarrierTranslation hInvariant n k F),
    norm_nonneg F]

/-- Canonical additive contraction action of the genuine `ℕ`-indexed finite
Wilson OS temporal translations. -/
noncomputable def toAdditiveContractionAction
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.AdditiveContractionAction ℕ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact {
    translate := R.realizableCarrierTranslation hInvariant n
    translate_zero := R.realizableCarrierTranslation_zero hInvariant n
    translate_add := by
      intro k l F
      have h := R.realizableCarrierTranslation_add hInvariant n l k F
      simpa [Nat.add_comm] using h
    norm_translate_le := G.realizableCarrierTranslation_norm_le n
    vacuumObservable_fixed := R.realizableCarrierTranslation_vacuumObservable
      hInvariant n
  }

@[simp] theorem toAdditiveContractionAction_translate
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (G.toAdditiveContractionAction n).translate k F =
      R.realizableCarrierTranslation hInvariant n k F :=
  rfl

/-- Completed physical Hilbert operator at `k` genuine lattice time steps. -/
noncomputable def realizablePhysicalOperator
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.PhysicalHilbert →L[ℝ] Pn.PhysicalHilbert := by
  dsimp only
  exact (G.toAdditiveContractionAction n).physicalOperator k

/-- The completed discrete operator agrees with the actual carrier translation
on every represented OS state. -/
theorem realizablePhysicalOperator_on_physicalState
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    G.realizablePhysicalOperator n k (Pn.physicalState F) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n k F) := by
  dsimp only
  exact (G.toAdditiveContractionAction n).physicalOperator_on_physicalState k F

/-- Every completed realizable discrete Wilson operator is contractive. -/
theorem realizablePhysicalOperator_norm_le
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    ‖G.realizablePhysicalOperator n k psi‖ ≤ ‖psi‖ := by
  exact (G.toAdditiveContractionAction n).physicalOperator_norm_le k psi

/-- Completed realizable discrete Wilson operators have operator norm at most
one. -/
theorem realizablePhysicalOperator_opNorm_le
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ) :
    ‖G.realizablePhysicalOperator n k‖ ≤ 1 := by
  exact (G.toAdditiveContractionAction n).physicalOperator_opNorm_le k

/-- The completed finite OS vacuum is fixed at every realizable lattice time. -/
theorem realizablePhysicalOperator_fixes_vacuum
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    G.realizablePhysicalOperator n k Pn.vacuum = Pn.vacuum := by
  dsimp only
  exact (G.toAdditiveContractionAction n).physicalOperator_fixes_vacuum k

/-- The completed discrete operators satisfy the exact natural-number semigroup
law. -/
theorem realizablePhysicalOperator_add
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k l : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    G.realizablePhysicalOperator n (k + l) psi =
      G.realizablePhysicalOperator n k
        (G.realizablePhysicalOperator n l psi) := by
  exact (G.toAdditiveContractionAction n).physicalOperator_add_apply k l psi

/-- The exact geometric decay generated on centered carrier observables extends
by density to every completed finite Wilson OS state orthogonal to the vacuum. -/
theorem realizablePhysicalOperator_vacuumOrthogonal_norm_le_pow
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (phi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
    (hphi : inner ℝ phi
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuum = 0) :
    ‖G.realizablePhysicalOperator n k phi‖ ≤
      (physicalYangMillsExact3320OneStepNormFactor S n) ^ k * ‖phi‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let A := G.toAdditiveContractionAction n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  apply A.physicalOperator_norm_decay_of_centered_core hPn k
    ((physicalYangMillsExact3320OneStepNormFactor S n) ^ k) ?_ phi hphi
  intro F
  have hcenter := G.centered_norm_le_pow n k F
  dsimp only at hcenter
  rw [← Pn.physicalState_vacuumCenteredCarrier]
  rw [A.physicalOperator_on_physicalState]
  rw [Pn.norm_physicalState, Pn.norm_physicalState]
  exact hcenter

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

end MathlibAnalytic
end MGAP4D

end
