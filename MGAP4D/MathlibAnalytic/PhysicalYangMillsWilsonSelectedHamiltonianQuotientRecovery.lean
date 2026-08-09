import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductSelectedSlowStateRecovery
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Generator-consistency form of the remaining selected moving-time Wilson
recovery obligation.

For the theorem-generated selected finite slow state `phi_n`, let

`psi_n = iota_n phi_n`,
`eta_n = iota_n (K_n^2 phi_n)`, and `h_n = a_n`.

The finite two-step Hamiltonian quotient

`(2 h_n)⁻¹ (psi_n - eta_n)`

is compared directly with the continuum right-Hamiltonian quotient

`(2 h_n)⁻¹ (psi_n - T(2 h_n) psi_n)`.

Their norm difference is required to tend to zero.  This is exactly the
first-order moving-time consistency hidden inside the raw `o(a_n)` vector
defect, but it does not assert any false moving-vector consequence of fixed-time
strong continuity.  No Hamiltonian-domain membership of the moving states is
assumed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
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
      S D halfExtent N hN beta hbeta Q.vacuumNormalized E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q.vacuumNormalized E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P) where
  quotientDefectExcess : ℕ → ℝ
  quotientDefectExcess_tendsto_zero : Tendsto quotientDefectExcess atTop (nhds 0)
  selectedHamiltonianQuotientDefect_le :
    ∀ n,
      let A := J.toMassFreeAmbientCarrier Q hInvariant
      let phi := physicalYangMillsSelectedFiniteSlowState C n
      let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
      let eta := A.excitationEmbed n ((K ∘L K) phi)
      let psi := A.excitationEmbed n phi
      let h := physicalYangMillsLatticeSpacingNNReal S n
      ‖((2 * S.latticeSpacing n)⁻¹ : ℝ) •
            ((psi : P.PhysicalHilbert) - (eta : P.PhysicalHilbert)) -
          T.rightHamiltonianDifferenceQuotient
            (psi : P.PhysicalHilbert) (h + h)‖ ≤
        quotientDefectExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery

set_option maxHeartbeats 800000

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
      S D halfExtent N hN beta hbeta Q.vacuumNormalized E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q.vacuumNormalized E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P}

/-- At every scale, the norm of the Hamiltonian-quotient discrepancy is exactly
the inverse two-step lattice time multiplied by the raw moving-time vector
defect. -/
theorem selectedHamiltonianQuotientDefect_eq_normalizedVectorDefect
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
      C P T J)
    (n : ℕ) :
    let A := J.toMassFreeAmbientCarrier Q hInvariant
    let phi := physicalYangMillsSelectedFiniteSlowState C n
    let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
    let eta := A.excitationEmbed n ((K ∘L K) phi)
    let psi := A.excitationEmbed n phi
    let h := physicalYangMillsLatticeSpacingNNReal S n
    ‖((2 * S.latticeSpacing n)⁻¹ : ℝ) •
          ((psi : P.PhysicalHilbert) - (eta : P.PhysicalHilbert)) -
        T.rightHamiltonianDifferenceQuotient
          (psi : P.PhysicalHilbert) (h + h)‖ =
      (2 * S.latticeSpacing n)⁻¹ *
        ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator (h + h)
            (psi : P.PhysicalHilbert)‖ := by
  dsimp only
  let A := J.toMassFreeAmbientCarrier Q hInvariant
  let phi := physicalYangMillsSelectedFiniteSlowState C n
  let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
  let eta := A.excitationEmbed n ((K ∘L K) phi)
  let psi := A.excitationEmbed n phi
  let h := physicalYangMillsLatticeSpacingNNReal S n
  have hdenpos : 0 < 2 * S.latticeSpacing n := by
    nlinarith [S.latticeSpacing_pos n]
  have htime : ((h + h : NNReal) : ℝ) = 2 * S.latticeSpacing n := by
    simp [h]
    ring
  change
    ‖((2 * S.latticeSpacing n)⁻¹ : ℝ) •
          ((psi : P.PhysicalHilbert) - (eta : P.PhysicalHilbert)) -
        (((h + h : NNReal) : ℝ)⁻¹ •
          ((psi : P.PhysicalHilbert) -
            T.toPhysicalSemigroup.operator (h + h)
              (psi : P.PhysicalHilbert)))‖ = _
  rw [htime]
  calc
    ‖((2 * S.latticeSpacing n)⁻¹ : ℝ) •
          ((psi : P.PhysicalHilbert) - (eta : P.PhysicalHilbert)) -
        (2 * S.latticeSpacing n)⁻¹ •
          ((psi : P.PhysicalHilbert) -
            T.toPhysicalSemigroup.operator (h + h)
              (psi : P.PhysicalHilbert))‖ =
      ‖-(((2 * S.latticeSpacing n)⁻¹ : ℝ) •
          ((eta : P.PhysicalHilbert) -
            T.toPhysicalSemigroup.operator (h + h)
              (psi : P.PhysicalHilbert)))‖ := by
        congr 1
        module
    _ = ‖((2 * S.latticeSpacing n)⁻¹ : ℝ) •
          ((eta : P.PhysicalHilbert) -
            T.toPhysicalSemigroup.operator (h + h)
              (psi : P.PhysicalHilbert))‖ := by
        rw [norm_neg]
    _ = ‖((2 * S.latticeSpacing n)⁻¹ : ℝ)‖ *
        ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator (h + h)
            (psi : P.PhysicalHilbert)‖ := by
        rw [norm_smul]
    _ = (2 * S.latticeSpacing n)⁻¹ *
        ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator (h + h)
            (psi : P.PhysicalHilbert)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenpos)]

/-- Hamiltonian-quotient consistency therefore theorem-generates #1593's raw
selected moving-time `o(a_n)` vector recovery. -/
noncomputable def toCommonProductSelectedSlowStateRecovery
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
      C P T J) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedSlowStateRecovery
      C P T J where
  vectorDefectExcess := V.quotientDefectExcess
  vectorDefectExcess_tendsto_zero := V.quotientDefectExcess_tendsto_zero
  selectedTwoStepVectorDefect_le := by
    intro n
    let A := J.toMassFreeAmbientCarrier Q hInvariant
    let phi := physicalYangMillsSelectedFiniteSlowState C n
    let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
    let eta := A.excitationEmbed n ((K ∘L K) phi)
    let psi := A.excitationEmbed n phi
    let h := physicalYangMillsLatticeSpacingNNReal S n
    have hdenpos : 0 < 2 * S.latticeSpacing n := by
      nlinarith [S.latticeSpacing_pos n]
    have hq0 := V.selectedHamiltonianQuotientDefect_le n
    have hq :
        (2 * S.latticeSpacing n)⁻¹ *
            ‖(eta : P.PhysicalHilbert) -
              T.toPhysicalSemigroup.operator (h + h)
                (psi : P.PhysicalHilbert)‖ ≤
          V.quotientDefectExcess n := by
      rw [← V.selectedHamiltonianQuotientDefect_eq_normalizedVectorDefect n]
      simpa [A, phi, K, eta, psi, h] using hq0
    have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt hdenpos)
    have hrecover :
        ‖(eta : P.PhysicalHilbert) -
              T.toPhysicalSemigroup.operator (h + h)
                (psi : P.PhysicalHilbert)‖ ≤
          (2 * S.latticeSpacing n) * V.quotientDefectExcess n := by
      calc
        ‖(eta : P.PhysicalHilbert) -
              T.toPhysicalSemigroup.operator (h + h)
                (psi : P.PhysicalHilbert)‖ =
          (2 * S.latticeSpacing n) *
            ((2 * S.latticeSpacing n)⁻¹ *
              ‖(eta : P.PhysicalHilbert) -
                T.toPhysicalSemigroup.operator (h + h)
                  (psi : P.PhysicalHilbert)‖) := by
            field_simp [ne_of_gt hdenpos]
        _ ≤ (2 * S.latticeSpacing n) * V.quotientDefectExcess n := hmul
    simpa [A, phi, K, eta, psi, h, mul_assoc] using hrecover

/-- Hence quotient consistency alone yields the reverse physical variational
mass inequality through the selected slow-state lane. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
      C P T J)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit :=
  V.toCommonProductSelectedSlowStateRecovery.physicalYangMillsMass_le_limit hSymmetric

/-- The quotient-consistency form also produces the nonzero continuum
vacuum-orthogonal excitation witness. -/
theorem excitationDomainWitness_nonempty
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
      C P T J)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    Nonempty T.PhysicalYangMillsExcitationDomainWitness :=
  V.toCommonProductSelectedSlowStateRecovery.excitationDomainWitness_nonempty hSymmetric

/-- With the independent forward common-carrier direction, quotient consistency
identifies the intrinsic Wilson rate limit with the physical variational mass.
No exact numerical evaluation is introduced here. -/
theorem limit_eq_physicalYangMillsMass
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery
      C P T J)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q.vacuumNormalized E R hInvariant C P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    C.limit = T.physicalYangMillsMass :=
  V.toCommonProductSelectedSlowStateRecovery.limit_eq_physicalYangMillsMass
    G hP hSymmetric

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSelectedHamiltonianQuotientRecovery

end

end MathlibAnalytic
end MGAP4D
