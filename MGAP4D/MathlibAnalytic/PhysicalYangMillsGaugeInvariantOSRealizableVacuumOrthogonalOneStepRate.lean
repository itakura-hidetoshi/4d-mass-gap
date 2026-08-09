import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePositiveHalfBoundedOneStepFactor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredQuadraticExcitation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableVacuumOrthogonalRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableVacuumOrthogonalRateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableVacuumOrthogonalRateSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableVacuumOrthogonalRateSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableVacuumOrthogonalRateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableVacuumOrthogonalRateSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

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

/-- The actual one-step translation followed by the dense OS state map. -/
def oneStepDenseStateLinearMap
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →ₗ[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  Pn.physicalStateLinearMap.comp
    (R.realizableCarrierTranslation hInvariant n 1)

@[simp] theorem oneStepDenseStateLinearMap_apply
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    A.oneStepDenseStateLinearMap n F =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
        (R.realizableCarrierTranslation hInvariant n 1 F) := by
  rfl

/-- The #1509 factorization supplies exactly the norm estimate needed to extend
the actual integer one-step map from represented OS states to the completed
finite physical Hilbert space.  The factor is used only as a boundedness receipt;
it will not define the mass rate. -/
theorem oneStepDenseStateLinearMap_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖A.oneStepDenseStateLinearMap n F‖ ≤
      A.transferFactor n *
        ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalStateLinearMap F‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [A.oneStepDenseStateLinearMap_apply,
    Pn.physicalStateLinearMap_apply,
    Pn.norm_physicalState, Pn.norm_physicalState]
  exact A.oneStep_norm_le n F

/-- The bounded completion of the *actual* integer one-step Wilson OS
translation.  Its full-space norm is deliberately not used as a mass-gap
quantity because the vacuum is a fixed vector. -/
noncomputable def oneStepPhysicalOperator
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  (A.oneStepDenseStateLinearMap n).extendOfNorm Pn.physicalStateLinearMap

/-- The completed one-step operator agrees with the realizable integer
translation on every represented OS state. -/
theorem oneStepPhysicalOperator_on_physicalState
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    A.oneStepPhysicalOperator n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F) =
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
        (R.realizableCarrierTranslation hInvariant n 1 F) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [← Pn.physicalStateLinearMap_apply,
    ← A.oneStepDenseStateLinearMap_apply]
  exact LinearMap.extendOfNorm_eq
    Pn.physicalStateLinearMap_denseRange
    ⟨A.transferFactor n, A.oneStepDenseStateLinearMap_norm_le n⟩ F

/-- The completed actual one-step map fixes the normalized finite OS vacuum. -/
theorem oneStepPhysicalOperator_fixes_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    A.oneStepPhysicalOperator n Pn.vacuum = Pn.vacuum := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  calc
    A.oneStepPhysicalOperator n Pn.vacuum =
        A.oneStepPhysicalOperator n (Pn.physicalState Pn.vacuumObservable) := rfl
    _ = Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n 1 Pn.vacuumObservable) :=
      A.oneStepPhysicalOperator_on_physicalState n Pn.vacuumObservable
    _ = Pn.physicalState Pn.vacuumObservable := by
      rw [R.realizableCarrierTranslation_vacuumObservable hInvariant n 1]
    _ = Pn.vacuum := rfl

/-- OS reflection/time exchange makes the actual realizable one-step carrier
translation symmetric for the finite OS inner product. -/
theorem oneStep_carrier_inner_eq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    inner ℝ (R.realizableCarrierTranslation hInvariant n 1 F) G =
      inner ℝ F (R.realizableCarrierTranslation hInvariant n 1 G) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [Pn.inner_eq_osBilinForm, Pn.inner_eq_osBilinForm]
  change
    D.osBilinForm Pn.omega
        (R.positiveTranslation n 1 (Pn.positiveTimeElement F))
        (Pn.positiveTimeElement G) =
      D.osBilinForm Pn.omega
        (Pn.positiveTimeElement F)
        (R.positiveTranslation n 1 (Pn.positiveTimeElement G))
  exact R.osBilinForm_positiveTranslation_exchange n 1
    (Pn.positiveTimeElement F) (Pn.positiveTimeElement G)

/-- Symmetry on the represented dense states extends to the whole finite
physical Hilbert space by the same `DenseRange.induction_on₂` argument used in
the continuum OS semigroup layer. -/
theorem oneStepPhysicalOperator_inner_eq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (psi phi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert) :
    inner ℝ (A.oneStepPhysicalOperator n psi) phi =
      inner ℝ psi (A.oneStepPhysicalOperator n phi) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  refine Pn.physicalStateLinearMap_denseRange.induction_on₂ ?_ ?_ psi phi
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F G
    rw [A.oneStepPhysicalOperator_on_physicalState,
      A.oneStepPhysicalOperator_on_physicalState,
      Pn.inner_physicalState_physicalState,
      Pn.inner_physicalState_physicalState]
    exact A.oneStep_carrier_inner_eq n F G

/-- The completed actual one-step operator preserves the finite physical
vacuum-orthogonal excitation sector. -/
theorem oneStepPhysicalOperator_mem_vacuumOrthogonal
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert)
    (hpsi : psi ∈
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumOrthogonal) :
    A.oneStepPhysicalOperator n psi ∈
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumOrthogonal := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [Pn.mem_vacuumOrthogonal_iff] at hpsi ⊢
  calc
    inner ℝ Pn.vacuum (A.oneStepPhysicalOperator n psi) =
        inner ℝ (A.oneStepPhysicalOperator n psi) Pn.vacuum :=
      real_inner_comm _ _
    _ = inner ℝ psi (A.oneStepPhysicalOperator n Pn.vacuum) :=
      A.oneStepPhysicalOperator_inner_eq n psi Pn.vacuum
    _ = inner ℝ psi Pn.vacuum := by
      rw [A.oneStepPhysicalOperator_fixes_vacuum n]
    _ = inner ℝ Pn.vacuum psi := real_inner_comm _ _
    _ = 0 := hpsi

/-- The intrinsic finite one-step transfer on the physical excitation sector. -/
noncomputable def vacuumOrthogonalOneStepOperator
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] Pn.VacuumOrthogonalHilbert := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    (A.oneStepPhysicalOperator n).restrict
      (p := Pn.vacuumOrthogonal) (q := Pn.vacuumOrthogonal)
      (fun psi hpsi => A.oneStepPhysicalOperator_mem_vacuumOrthogonal n psi hpsi)

/-- The physically relevant finite transfer factor: the operator norm of the
actual one-step transfer restricted to `Ωₙ⊥`.

Unlike the full operator norm, this quantity can be strictly below one because
the fixed vacuum mode has been removed. -/
def vacuumOrthogonalTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  ‖A.vacuumOrthogonalOneStepOperator n‖

/-- The intrinsic excitation-sector factor is automatically nonnegative. -/
theorem vacuumOrthogonalTransferFactor_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.vacuumOrthogonalTransferFactor n :=
  norm_nonneg _

/-- The excitation-sector one-step norm controls every centered represented OS
observable.  This is the exact finite estimate consumed by the realizable
integer-time iteration spine. -/
theorem oneStep_centered_norm_le_vacuumOrthogonalTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖R.realizableCarrierTranslation hInvariant n 1
        (Pn.vacuumCenteredCarrier F)‖ ≤
      A.vacuumOrthogonalTransferFactor n * ‖Pn.vacuumCenteredCarrier F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let x : Pn.VacuumOrthogonalHilbert :=
    Pn.centeredPhysicalExcitation hPn F
  have hx := (A.vacuumOrthogonalOneStepOperator n).le_opNorm x
  change
    ‖R.realizableCarrierTranslation hInvariant n 1
        (Pn.vacuumCenteredCarrier F)‖ ≤
      A.vacuumOrthogonalTransferFactor n * ‖Pn.vacuumCenteredCarrier F‖
  have hop :
      ((A.vacuumOrthogonalOneStepOperator n x : Pn.VacuumOrthogonalHilbert) :
        Pn.PhysicalHilbert) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)) := by
    change A.oneStepPhysicalOperator n
        (Pn.physicalState (Pn.vacuumCenteredCarrier F)) = _
    exact A.oneStepPhysicalOperator_on_physicalState n
      (Pn.vacuumCenteredCarrier F)
  rw [← Pn.norm_physicalState]
  rw [← Pn.norm_physicalState]
  simpa only [hop, vacuumOrthogonalTransferFactor, x,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.centeredPhysicalExcitation]
    using hx

/-- Canonical one-step certificate with the physically correct factor
`rₙ = ‖T_{n,1}|_{Ωₙ⊥}‖`. -/
noncomputable def toVacuumOrthogonalRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.vacuumOrthogonalTransferFactor where
  transferFactor_nonneg := A.vacuumOrthogonalTransferFactor_nonneg
  oneStep_centered_norm_le := A.oneStep_centered_norm_le_vacuumOrthogonalTransferFactor

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- Positive continuum-rate data for the intrinsic excitation-sector one-step
Wilson norms.

The sequence entering the logarithm is definitionally

`rₙ = ‖T_{n,1}|_{Ωₙ⊥}‖`,

so the fixed vacuum eigenvalue no longer forces the rate to vanish. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  boundedAnalysis :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant
  transferFactor_pos :
    ∀ n, 0 < boundedAnalysis.vacuumOrthogonalTransferFactor n
  transferFactor_le_one :
    ∀ n, boundedAnalysis.vacuumOrthogonalTransferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n =>
        -Real.log (boundedAnalysis.vacuumOrthogonalTransferFactor n) /
          S.latticeSpacing n)
      atTop (nhds mass)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate

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

/-- The intrinsic excitation-sector norm gives the actual integer-time one-step
certificate used by the discrete/floor continuum transfer route. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.boundedAnalysis.vacuumOrthogonalTransferFactor :=
  A.boundedAnalysis.toVacuumOrthogonalRealizableOneStepGapCertificate

/-- Package the physically correct finite factor into the generic discrete
logarithmic-rate limit. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDiscreteTransferRateLimit
      S.latticeSpacing A.boundedAnalysis.vacuumOrthogonalTransferFactor where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto

/-- The finite mass rate is literally the logarithmic decay rate of the actual
one-step Wilson transfer restricted to the finite physical excitation sector. -/
def massRate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  -Real.log (A.boundedAnalysis.vacuumOrthogonalTransferFactor n) /
    S.latticeSpacing n

@[simp] theorem massRate_eq_vacuumOrthogonal_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.massRate n =
      -Real.log ‖A.boundedAnalysis.vacuumOrthogonalOneStepOperator n‖ /
        S.latticeSpacing n :=
  rfl

/-- The intrinsic excitation-sector finite rates converge to the derived
continuum mass. -/
theorem massRate_tendsto_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto A.massRate atTop (nhds A.mass) := by
  simpa only [massRate] using A.massRate_tendsto

/-- Floor-selected powers of the actual excitation-sector one-step norm converge
to the continuum exponential with the mass derived from those norms. -/
theorem floorPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (A.boundedAnalysis.vacuumOrthogonalTransferFactor n) ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact A.toPositiveDiscreteTransferRateLimit.floorPow_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableVacuumOrthogonalDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end