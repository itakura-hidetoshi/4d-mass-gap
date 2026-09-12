import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonMassFreeAmbientTwoStepRecovery
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance selectedRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance selectedRecoverySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance selectedRecoverySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance selectedRecoverySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance selectedRecoverySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance selectedRecoverySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Canonical theorem-generated finite Wilson slow state, independent of any
continuum recovery package.  The existence theorem is #1569's actual completed
finite excitation result. -/
noncomputable def physicalYangMillsSelectedFiniteSlowState
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert :=
  Classical.choose (exists_physicalYangMillsFiniteUnitSlowState C n)

@[simp] theorem physicalYangMillsSelectedFiniteSlowState_norm
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖physicalYangMillsSelectedFiniteSlowState C n‖ = 1 :=
  (Classical.choose_spec (exists_physicalYangMillsFiniteUnitSlowState C n)).1

theorem physicalYangMillsSelectedFiniteSlowState_energy_lt_rate_add_spacing
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy C n
        (physicalYangMillsSelectedFiniteSlowState C n) <
      physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n + S.latticeSpacing n :=
  (Classical.choose_spec (exists_physicalYangMillsFiniteUnitSlowState C n)).2

/-- Minimal Mosco/Gamma-limsup recovery data for the reverse Wilson mass lane.

The ambient finite-to-continuum Hilbert carrier is already mass-free.  Instead
of a rate-scaled two-step residual for every unit finite excitation, this
structure asks for it only along the theorem-generated slow state sequence
selected above.  This is exactly the sequence used by the variational reverse
inequality. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.toWeakStarBridge) (hInvariant := hInvariant) P) where
  vectorDefectExcess : ℕ → ℝ
  vectorDefectExcess_tendsto_zero : Tendsto vectorDefectExcess atTop (nhds 0)
  selectedTwoStepVectorDefect_le :
    ∀ n,
      let phi := physicalYangMillsSelectedFiniteSlowState C n
      let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
      let eta := A.excitationEmbed n ((K ∘L K) phi)
      let psi := A.excitationEmbed n phi
      ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator
            (physicalYangMillsLatticeSpacingNNReal S n +
              physicalYangMillsLatticeSpacingNNReal S n)
            (psi : P.PhysicalHilbert)‖ ≤
        2 * S.latticeSpacing n * vectorDefectExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.toWeakStarBridge) (hInvariant := hInvariant) P}

/-- Selected finite slow state embedded in the continuum excitation Hilbert
space by the theorem-generated mass-free carrier embedding. -/
noncomputable def embeddedSelectedSlowState
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (n : ℕ) : P.VacuumOrthogonalHilbert :=
  A.excitationEmbed n (physicalYangMillsSelectedFiniteSlowState C n)

@[simp] theorem embeddedSelectedSlowState_norm
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (n : ℕ) : ‖V.embeddedSelectedSlowState n‖ = 1 := by
  rw [embeddedSelectedSlowState, A.excitationEmbed_norm,
    physicalYangMillsSelectedFiniteSlowState_norm]

/-- The selected vector `o(a_n)` residual implies the scalar two-step defect
bound needed by the moving-Rayleigh argument.  This is exactly #1576's
Cauchy--Schwarz reduction, specialized to the canonical slow state. -/
theorem selectedSlowState_twoStepDefectRate_le_finiteEnergy_add_excess
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (n : ℕ) :
    T.twoStepCorrelationDefectRate
        (physicalYangMillsLatticeSpacingNNReal S n)
        ((V.embeddedSelectedSlowState n : P.VacuumOrthogonalHilbert) :
          P.PhysicalHilbert) ≤
      physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy C n
          (physicalYangMillsSelectedFiniteSlowState C n) +
        V.vectorDefectExcess n := by
  let phi := physicalYangMillsSelectedFiniteSlowState C n
  let h := physicalYangMillsLatticeSpacingNNReal S n
  let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
  let etaFinite := (K ∘L K) phi
  let psiOrth : P.VacuumOrthogonalHilbert := A.excitationEmbed n phi
  let etaOrth : P.VacuumOrthogonalHilbert := A.excitationEmbed n etaFinite
  let psi : P.PhysicalHilbert := (psiOrth : P.PhysicalHilbert)
  let eta : P.PhysicalHilbert := (etaOrth : P.PhysicalHilbert)
  have hphi : ‖phi‖ = 1 := by
    simpa [phi] using physicalYangMillsSelectedFiniteSlowState_norm C n
  have hdenpos : 0 < 2 * S.latticeSpacing n := by
    nlinarith [S.latticeSpacing_pos n]
  have hpsiNorm : ‖psi‖ = 1 := by
    change ‖A.excitationEmbed n phi‖ = 1
    rw [A.excitationEmbed_norm n phi, hphi]
  have hinnerIso0 :=
    ContinuousLinearMap.inner_map_map_of_norm_map
      (A.excitationEmbed n) (fun x => A.excitationEmbed_norm n x)
      etaFinite phi
  have hinnerIso : inner ℝ eta psi = inner ℝ etaFinite phi := by
    simpa [eta, psi, etaOrth, psiOrth] using hinnerIso0
  have hvec0 := V.selectedTwoStepVectorDefect_le n
  have hvec :
      ‖eta - T.toPhysicalSemigroup.operator (h + h) psi‖ ≤
        2 * S.latticeSpacing n * V.vectorDefectExcess n := by
    simpa [phi, h, K, etaFinite, psiOrth, etaOrth, psi, eta] using hvec0
  have hinner :
      inner ℝ
          (eta - T.toPhysicalSemigroup.operator (h + h) psi)
          psi ≤
        2 * S.latticeSpacing n * V.vectorDefectExcess n := by
    calc
      inner ℝ
          (eta - T.toPhysicalSemigroup.operator (h + h) psi)
          psi ≤
        ‖eta - T.toPhysicalSemigroup.operator (h + h) psi‖ * ‖psi‖ :=
          real_inner_le_norm _ _
      _ = ‖eta - T.toPhysicalSemigroup.operator (h + h) psi‖ := by
        rw [hpsiNorm, mul_one]
      _ ≤ 2 * S.latticeSpacing n * V.vectorDefectExcess n := hvec
  rw [inner_sub_left, hinnerIso,
    real_inner_comm psi (T.toPhysicalSemigroup.operator (h + h) psi)] at hinner
  have hnum :
      ‖psi‖ ^ 2 -
          inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi) ≤
        1 - inner ℝ etaFinite phi +
          (2 * S.latticeSpacing n) * V.vectorDefectExcess n := by
    calc
      ‖psi‖ ^ 2 -
          inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi) =
        1 - inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi) := by
          rw [hpsiNorm]
          norm_num
      _ =
        (1 - inner ℝ etaFinite phi) +
          (inner ℝ etaFinite phi -
            inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi)) := by
          ring
      _ ≤
        (1 - inner ℝ etaFinite phi) +
          (2 * S.latticeSpacing n) * V.vectorDefectExcess n := by
          simpa [add_comm] using
            add_le_add_left hinner (1 - inner ℝ etaFinite phi)
      _ =
        1 - inner ℝ etaFinite phi +
          (2 * S.latticeSpacing n) * V.vectorDefectExcess n := by
          rfl
  have hquot :
      (‖psi‖ ^ 2 -
          inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi)) /
            (2 * S.latticeSpacing n) ≤
        (1 - inner ℝ etaFinite phi +
            (2 * S.latticeSpacing n) * V.vectorDefectExcess n) /
          (2 * S.latticeSpacing n) :=
    (div_le_div_iff_of_pos_right hdenpos).2 hnum
  change
    (‖psi‖ ^ 2 -
        inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi)) /
          (2 * S.latticeSpacing n) ≤
      (1 - inner ℝ etaFinite phi) / (2 * S.latticeSpacing n) +
        V.vectorDefectExcess n
  calc
    (‖psi‖ ^ 2 -
        inner ℝ psi (T.toPhysicalSemigroup.operator (h + h) psi)) /
          (2 * S.latticeSpacing n) ≤
      (1 - inner ℝ etaFinite phi +
          (2 * S.latticeSpacing n) * V.vectorDefectExcess n) /
        (2 * S.latticeSpacing n) := hquot
    _ =
      (1 - inner ℝ etaFinite phi) / (2 * S.latticeSpacing n) +
        V.vectorDefectExcess n := by
      field_simp [ne_of_gt hdenpos, ne_of_gt (S.latticeSpacing_pos n)]

/-- Scalar dominator for the selected slow state. -/
def selectedSlowStateDominator
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (n : ℕ) : ℝ :=
  physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
      C.boundedAnalysis n +
    S.latticeSpacing n + V.vectorDefectExcess n

theorem embeddedSelectedSlowState_twoStepDefectRate_lt_dominator
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (n : ℕ) :
    T.twoStepCorrelationDefectRate
        (physicalYangMillsLatticeSpacingNNReal S n)
        ((V.embeddedSelectedSlowState n : P.VacuumOrthogonalHilbert) :
          P.PhysicalHilbert) <
      V.selectedSlowStateDominator n := by
  have hcompat := V.selectedSlowState_twoStepDefectRate_le_finiteEnergy_add_excess n
  have hslow := physicalYangMillsSelectedFiniteSlowState_energy_lt_rate_add_spacing C n
  unfold selectedSlowStateDominator
  linarith

theorem selectedSlowStateDominator_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A) :
    Tendsto V.selectedSlowStateDominator atTop (nhds C.limit) := by
  have hsum :=
    (C.rate_tendsto_limit.add S.latticeSpacing_tendsto_zero).add
      V.vectorDefectExcess_tendsto_zero
  simpa only [selectedSlowStateDominator, add_zero] using hsum

theorem correctedSelectedSlowStateDominator_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A) :
    Tendsto
      (fun n =>
        V.selectedSlowStateDominator n /
          (1 - 2 * S.latticeSpacing n * V.selectedSlowStateDominator n))
      atTop (nhds C.limit) := by
  simpa only [coe_physicalYangMillsLatticeSpacingNNReal] using
    tendsto_dominator_div_one_sub_two_mul_width_mul_dominator
      (h := fun n => physicalYangMillsLatticeSpacingNNReal S n)
      (M := V.selectedSlowStateDominator)
      (physicalYangMillsLatticeSpacingNNReal_coe_tendsto_zero S)
      V.selectedSlowStateDominator_tendsto_limit

theorem eventually_selectedSlowStateDominator_correction_lt_one
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A) :
    ∀ᶠ n in atTop,
      2 * S.latticeSpacing n * V.selectedSlowStateDominator n < 1 := by
  simpa only [coe_physicalYangMillsLatticeSpacingNNReal] using
    eventually_two_mul_width_mul_dominator_lt_one
      (h := fun n => physicalYangMillsLatticeSpacingNNReal S n)
      (M := V.selectedSlowStateDominator)
      (physicalYangMillsLatticeSpacingNNReal_coe_tendsto_zero S)
      V.selectedSlowStateDominator_tendsto_limit

/-- Selected-sequence vector recovery alone is sufficient for the reverse
variational mass inequality. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    V.correctedSelectedSlowStateDominator_tendsto_limit
  filter_upwards [V.eventually_selectedSlowStateDominator_correction_lt_one] with n hn
  let h := physicalYangMillsLatticeSpacingNNReal S n
  let psi : P.PhysicalHilbert :=
    (V.embeddedSelectedSlowState n : P.VacuumOrthogonalHilbert)
  have hh : 0 < h := physicalYangMillsLatticeSpacingNNReal_pos S n
  have hpsi : ‖psi‖ = 1 := by
    simpa [psi] using V.embeddedSelectedSlowState_norm n
  have hdM : T.twoStepCorrelationDefectRate h psi ≤ V.selectedSlowStateDominator n := by
    exact le_of_lt (V.embeddedSelectedSlowState_twoStepDefectRate_lt_dominator n)
  have hcorrection : 2 * (h : ℝ) * V.selectedSlowStateDominator n < 1 := by
    simpa [h] using hn
  have hne :
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 :=
    T.timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_dominatorCorrection_lt_one
      hSymmetric hh hpsi hdM hcorrection
  have hpsiOrth : psi ∈ P.vacuumOrthogonal := by
    exact (V.embeddedSelectedSlowState n).property
  have horth :
      inner ℝ
        (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)
        P.vacuum = 0 :=
    T.inner_timeAverageClosedRightHamiltonianDomain_vacuum_eq_zero_of_innerSymmetric
      hSymmetric h hpsiOrth
  have hmass :
      T.physicalYangMillsMass ≤ T.timeAverageClosedRayleighQuotient h psi := by
    exact T.physicalYangMillsMass_le_rayleigh
      ⟨T.timeAverageClosedRightHamiltonianDomain h psi, hne, horth, rfl⟩
  have hrayleigh :=
    T.timeAverageClosedRayleighQuotient_le_dominator
      hSymmetric hh hpsi hdM hcorrection
  exact hmass.trans hrayleigh

/-- The same selected recovery produces at least one genuine excitation-domain
witness. -/
theorem excitationDomainWitness_nonempty
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    Nonempty T.PhysicalYangMillsExcitationDomainWitness := by
  have hexists : ∃ n,
      2 * S.latticeSpacing n * V.selectedSlowStateDominator n < 1 :=
    V.eventually_selectedSlowStateDominator_correction_lt_one.exists
  rcases hexists with ⟨n, hn⟩
  let h := physicalYangMillsLatticeSpacingNNReal S n
  let psi : P.PhysicalHilbert :=
    (V.embeddedSelectedSlowState n : P.VacuumOrthogonalHilbert)
  have hh : 0 < h := physicalYangMillsLatticeSpacingNNReal_pos S n
  have hpsi : ‖psi‖ = 1 := by
    simpa [psi] using V.embeddedSelectedSlowState_norm n
  have hdM : T.twoStepCorrelationDefectRate h psi ≤ V.selectedSlowStateDominator n := by
    exact le_of_lt (V.embeddedSelectedSlowState_twoStepDefectRate_lt_dominator n)
  have hcorrection : 2 * (h : ℝ) * V.selectedSlowStateDominator n < 1 := by
    simpa [h] using hn
  have hne :
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 :=
    T.timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_dominatorCorrection_lt_one
      hSymmetric hh hpsi hdM hcorrection
  have hpsiOrth : psi ∈ P.vacuumOrthogonal := by
    exact (V.embeddedSelectedSlowState n).property
  have horth :
      inner ℝ
        (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert)
        P.vacuum = 0 :=
    T.inner_timeAverageClosedRightHamiltonianDomain_vacuum_eq_zero_of_innerSymmetric
      hSymmetric h hpsiOrth
  exact ⟨{
    state := T.timeAverageClosedRightHamiltonianDomain h psi
    state_ne_zero := hne
    state_orthogonal := horth
  }⟩

/-- Minimal selected-slow-state reverse recovery plus the independent
continuum-to-finite common-carrier direction identify the intrinsic Wilson rate
limit with the physical Yang--Mills variational mass. -/
theorem limit_eq_physicalYangMillsMass
    (V : PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery
      C P T A)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    C.limit = T.physicalYangMillsMass := by
  let W : T.PhysicalYangMillsExcitationDomainWitness :=
    Classical.choice (V.excitationDomainWitness_nonempty hSymmetric)
  exact le_antisymm
    (G.limit_le_physicalYangMillsMass_without_strictPos hP W)
    (V.physicalYangMillsMass_le_limit hSymmetric)

end PhysicalYangMillsEvenPeriodicWilsonOSSelectedSlowStateTwoStepRecovery

end MathlibAnalytic
end MGAP4D

end