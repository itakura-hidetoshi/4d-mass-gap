import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePositiveHalfBoundedOneStepFactor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The vacuum-centered carrier sector before the OS null quotient.

It is the kernel of the actual OS-state expectation on positive-time carrier
observables.  This is the finite carrier analogue of the vacuum-orthogonal
physical Hilbert sector, and unlike the full carrier it does not contain the
constant vacuum direction. -/
def centeredCarrierSubmodule (P : D.OSPreHilbertData) : Submodule ℝ P.Carrier where
  carrier := {F | P.omega F.toGaugeInvariant = 0}
  zero_mem' := by
    change P.omega (0 : physicalYangMillsGaugeInvariantObservableSubalgebra S) = 0
    exact map_zero P.omega
  add_mem' := by
    intro F G hF hG
    change P.omega (F.toGaugeInvariant + G.toGaugeInvariant) = 0
    rw [map_add, hF, hG, add_zero]
  smul_mem' := by
    intro c F hF
    change P.omega (c • F.toGaugeInvariant) = 0
    rw [map_smul, hF, smul_zero]

/-- The normed real carrier used for intrinsic centered one-step operator norms. -/
abbrev CenteredCarrier (P : D.OSPreHilbertData) : Type :=
  P.centeredCarrierSubmodule

/-- Vacuum centering lands in the expectation-zero carrier sector whenever the
OS state is normalized. -/
theorem vacuumCenteredCarrier_mem_centeredCarrierSubmodule
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized)
    (F : P.Carrier) :
    P.vacuumCenteredCarrier F ∈ P.centeredCarrierSubmodule := by
  change P.omega (P.vacuumCenteredCarrier F).toGaugeInvariant = 0
  unfold vacuumCenteredCarrier
  change P.omega
    (F.toGaugeInvariant -
      P.omega F.toGaugeInvariant •
        (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S)) = 0
  calc
    P.omega
        (F.toGaugeInvariant -
          P.omega F.toGaugeInvariant •
            (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S)) =
      P.omega F.toGaugeInvariant -
        P.omega
          (P.omega F.toGaugeInvariant •
            (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S)) := by
      exact map_sub P.omega _ _
    _ = 0 := by
      rw [map_smul, hP]
      simp

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

local instance realizableCenteredRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableCenteredRateSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableCenteredRateSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableCenteredRateSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableCenteredRateSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableCenteredRateSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

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

/-- Actual finite Wilson stationarity makes every realizable integer-time
carrier translation preserve the expectation-zero sector. -/
theorem realizableCarrierTranslation_mem_centeredCarrierSubmodule
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.realizableCarrierTranslation hInvariant n k (F : Pn.Carrier) ∈
      Pn.centeredCarrierSubmodule := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change Pn.omega
      (R.realizableCarrierTranslation hInvariant n k (F : Pn.Carrier)).toGaugeInvariant = 0
  rw [R.realizableCarrierTranslation_omega_stationary hInvariant n k (F : Pn.Carrier)]
  exact F.property

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

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

/-- The actual one-step carrier translation restricted to the finite
expectation-zero sector.  Its underlying map is fixed by the Wilson dynamics;
stationarity proves that the codomain is again centered. -/
noncomputable def centeredOneStepLinearMap
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.CenteredCarrier →ₗ[ℝ] Pn.CenteredCarrier := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    { toFun := fun F =>
        ⟨R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier),
          R.realizableCarrierTranslation_mem_centeredCarrierSubmodule
            hInvariant n 1 F⟩
      map_add' := by
        intro F G
        apply Subtype.ext
        change
          R.realizableCarrierTranslation hInvariant n 1
              ((F : Pn.Carrier) + (G : Pn.Carrier)) =
            R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier) +
              R.realizableCarrierTranslation hInvariant n 1 (G : Pn.Carrier)
        exact (R.realizableCarrierTranslation hInvariant n 1).map_add
          (F : Pn.Carrier) (G : Pn.Carrier)
      map_smul' := by
        intro c F
        apply Subtype.ext
        change
          R.realizableCarrierTranslation hInvariant n 1
              (c • (F : Pn.Carrier)) =
            c • R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier)
        exact (R.realizableCarrierTranslation hInvariant n 1).map_smul
          c (F : Pn.Carrier) }

/-- #1509's actual positive-half factorization supplies continuity of the
centered restriction, but the operator itself is exactly the restricted
integer one-step Wilson translation. -/
noncomputable def centeredOneStepOperator
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.CenteredCarrier →L[ℝ] Pn.CenteredCarrier := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    (A.centeredOneStepLinearMap n).mkContinuous
      (A.transferFactor n) (by
        intro F
        simpa only [centeredOneStepLinearMap] using
          A.oneStep_norm_le n (F : Pn.Carrier))

@[simp] theorem centeredOneStepOperator_apply_coe
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    ((A.centeredOneStepOperator n F :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) =
      R.realizableCarrierTranslation hInvariant n 1
        (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :=
  rfl

/-- The intrinsic finite mass-gap factor is the operator norm on the centered
carrier sector, not the full carrier norm.  The constant vacuum is absent from
this domain by construction. -/
def centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  ‖A.centeredOneStepOperator n‖

/-- The centered factor is nonnegative. -/
theorem centeredTransferFactor_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.centeredTransferFactor n := by
  change 0 ≤ ‖A.centeredOneStepOperator n‖
  exact norm_nonneg (A.centeredOneStepOperator n)

/-- The intrinsic centered operator norm is bounded by #1509's theorem-generated
positive-half/synthesis product factor. -/
theorem centeredTransferFactor_le_transferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.centeredTransferFactor n ≤ A.transferFactor n := by
  apply ContinuousLinearMap.opNorm_le_bound
    (A.centeredOneStepOperator n) (A.transferFactor_nonneg n)
  intro F
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  simpa only [centeredOneStepOperator_apply_coe] using
    A.oneStep_norm_le n (F : Pn.Carrier)

/-- The #1509 full-carrier product factor necessarily dominates one because it
also controls the normalized vacuum, which is fixed by the actual one-step
translation.  This theorem records why that full factor cannot itself be a
strict mass-gap rate. -/
theorem one_le_transferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    1 ≤ A.transferFactor n := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hnormVacuumObservable : ‖Pn.vacuumObservable‖ = 1 := by
    rw [← Pn.norm_physicalState]
    change ‖Pn.vacuum‖ = 1
    exact Pn.norm_vacuum
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)
  have hbound := A.oneStep_norm_le n Pn.vacuumObservable
  rw [R.realizableCarrierTranslation_vacuumObservable hInvariant n 1,
    hnormVacuumObservable] at hbound
  simpa using hbound

/-- Therefore imposing a unit upper bound on #1509's full-carrier factor forces
that auxiliary factor to be exactly one. -/
theorem transferFactor_eq_one_of_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (h : ∀ n, A.transferFactor n ≤ 1)
    (n : ℕ) :
    A.transferFactor n = 1 :=
  le_antisymm (h n) (A.one_le_transferFactor n)

/-- A centered carrier point canonically represented by vacuum centering. -/
noncomputable def vacuumCenteredCarrierPoint
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    ⟨Pn.vacuumCenteredCarrier F,
      Pn.vacuumCenteredCarrier_mem_centeredCarrierSubmodule
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) F⟩

/-- The centered restriction directly supplies the actual one-step gap
certificate with factor definitionally equal to its intrinsic operator norm. -/
noncomputable def toCenteredOperatorNormRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant A.centeredTransferFactor where
  transferFactor_nonneg := A.centeredTransferFactor_nonneg
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := A.vacuumCenteredCarrierPoint n F
    have h := (A.centeredOneStepOperator n).le_opNorm Fc
    change
      ‖R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)‖ ≤
        A.centeredTransferFactor n * ‖Pn.vacuumCenteredCarrier F‖
    simpa only [Fc, vacuumCenteredCarrierPoint, centeredOneStepOperator_apply_coe,
      centeredTransferFactor] using h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- Positive continuum-rate data for the intrinsic vacuum-centered one-step
Wilson operator norms.

All numerical data now refer to the actual excitation-sector transfer:
`r_n = ||T_{n,1}|_{centered}||`.  The vacuum eigenvalue is removed before the
logarithmic rate is formed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
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
  transferFactor_pos : ∀ n, 0 < boundedAnalysis.centeredTransferFactor n
  transferFactor_le_one : ∀ n, boundedAnalysis.centeredTransferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n =>
        -Real.log (boundedAnalysis.centeredTransferFactor n) / S.latticeSpacing n)
      atTop (nhds mass)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

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

/-- The intrinsic centered operator norm supplies the genuine integer-time
one-step Wilson gap certificate. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.boundedAnalysis.centeredTransferFactor :=
  A.boundedAnalysis.toCenteredOperatorNormRealizableOneStepGapCertificate

/-- Package the actual centered one-step operator norms into the generic
positive discrete logarithmic-rate limit used by the floor continuum spine. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDiscreteTransferRateLimit
      S.latticeSpacing A.boundedAnalysis.centeredTransferFactor where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto

/-- The finite physical mass rate is literally the logarithmic decay rate of
the actual vacuum-centered integer one-step Wilson operator. -/
def massRate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  -Real.log (A.boundedAnalysis.centeredTransferFactor n) / S.latticeSpacing n

@[simp] theorem massRate_eq_centered_oneStep_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.massRate n =
      -Real.log ‖A.boundedAnalysis.centeredOneStepOperator n‖ /
        S.latticeSpacing n :=
  rfl

/-- The intrinsic centered finite rates converge to the derived continuum mass. -/
theorem massRate_tendsto_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto A.massRate atTop (nhds A.mass) := by
  simpa only [massRate] using A.massRate_tendsto

/-- For every fixed physical time, the floor-selected powers of the actual
centered one-step operator norm converge to the continuum exponential with the
mass derived from those norms. -/
theorem floorPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (A.boundedAnalysis.centeredTransferFactor n) ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact A.toPositiveDiscreteTransferRateLimit.floorPow_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end