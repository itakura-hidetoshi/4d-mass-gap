import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActualExcitationTwoStepPositiveLogRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateToPhysicalMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupRayleighDominatorLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageExcitationGraphRegularization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance scalarReverseSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance scalarReverseSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance scalarReverseSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance scalarReverseSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance scalarReverseSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance scalarReverseSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The positive lattice spacing bundled as an `NNReal` averaging width. -/
def physicalYangMillsLatticeSpacingNNReal
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) : NNReal :=
  ⟨S.latticeSpacing n, (S.latticeSpacing_pos n).le⟩

@[simp] theorem coe_physicalYangMillsLatticeSpacingNNReal
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    (physicalYangMillsLatticeSpacingNNReal S n : ℝ) = S.latticeSpacing n :=
  rfl

theorem physicalYangMillsLatticeSpacingNNReal_pos
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    0 < physicalYangMillsLatticeSpacingNNReal S n := by
  change 0 < S.latticeSpacing n
  exact S.latticeSpacing_pos n

theorem physicalYangMillsLatticeSpacingNNReal_coe_tendsto_zero
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    Tendsto
      (fun n => (physicalYangMillsLatticeSpacingNNReal S n : ℝ))
      atTop (nhds 0) := by
  simpa using S.latticeSpacing_tendsto_zero

/-- The actual finite Wilson two-step quadratic energy on the completed
vacuum-orthogonal excitation Hilbert space. -/
def physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy
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
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) : ℝ :=
  (1 - inner ℝ
      (((C.boundedAnalysis.physicalExcitationOneStepOperator n) ∘L
        (C.boundedAnalysis.physicalExcitationOneStepOperator n)) phi) phi) /
    (2 * S.latticeSpacing n)

/-- At every scale the actual finite Wilson excitation operator supplies a unit
slow state whose two-step energy is below its intrinsic one-step logarithmic
rate plus one lattice spacing.  The state is theorem-generated; it is not part
of the reverse-transfer data. -/
theorem exists_physicalYangMillsFiniteUnitSlowState
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
    ∃ phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert,
      ‖phi‖ = 1 ∧
      physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy C n phi <
        physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
          C.boundedAnalysis n + S.latticeSpacing n := by
  simpa only [physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy]
    using
      C.boundedAnalysis.exists_physicalExcitationUnitTwoStepEnergy_lt_centeredLogRate_add
        n (C.transferFactor_pos n) (S.latticeSpacing_pos n)

/-- Mass-free finite-to-continuum recovery data at the scalar two-step level.

The map embeds the actual completed finite Wilson excitation Hilbert space into
the continuum excitation Hilbert space isometrically.  The only dynamical
compatibility required is a one-sided estimate for the scalar two-step defect
rate, with an additive excess tending to zero.  No mass value, spectral vector,
operator intertwining, compactness field, or target exact number is stored. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer
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
    (T : P.StronglyContinuousPhysicalSemigroup) where
  excitationEmbed :
    (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert →L[ℝ]
        P.VacuumOrthogonalHilbert
  excitationEmbed_norm :
    ∀ n phi, ‖excitationEmbed n phi‖ = ‖phi‖
  defectRateExcess : ℕ → ℝ
  defectRateExcess_tendsto_zero : Tendsto defectRateExcess atTop (nhds 0)
  twoStepDefectRate_le_finiteEnergy_add_excess :
    ∀ n phi, ‖phi‖ = 1 →
      T.twoStepCorrelationDefectRate
          (physicalYangMillsLatticeSpacingNNReal S n)
          ((excitationEmbed n phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) ≤
        physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy C n phi +
          defectRateExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer

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

/-- Canonically select the theorem-generated finite slow state with additive
error equal to one lattice spacing. -/
noncomputable def finiteSlowState
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert :=
  Classical.choose (exists_physicalYangMillsFiniteUnitSlowState C n)

@[simp] theorem finiteSlowState_norm
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) : ‖V.finiteSlowState n‖ = 1 :=
  (Classical.choose_spec (exists_physicalYangMillsFiniteUnitSlowState C n)).1

theorem finiteSlowState_energy_lt_rate_add_spacing
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) :
    physicalYangMillsEvenPeriodicWilsonOSActualTwoStepExcitationEnergy
        C n (V.finiteSlowState n) <
      physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n + S.latticeSpacing n :=
  (Classical.choose_spec (exists_physicalYangMillsFiniteUnitSlowState C n)).2

/-- The selected finite slow state embedded in the continuum excitation
subspace. -/
noncomputable def embeddedSlowState
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) : P.VacuumOrthogonalHilbert :=
  V.excitationEmbed n (V.finiteSlowState n)

@[simp] theorem embeddedSlowState_norm
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) : ‖V.embeddedSlowState n‖ = 1 := by
  rw [embeddedSlowState, V.excitationEmbed_norm, V.finiteSlowState_norm]

/-- Scalar dominator obtained from the intrinsic finite Wilson rate, the chosen
finite slow-state error `a_n`, and the finite-to-continuum scalar excess. -/
def slowStateDominator
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) : ℝ :=
  physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
      C.boundedAnalysis n +
    S.latticeSpacing n + V.defectRateExcess n

/-- The continuum two-step defect rate of the embedded actual finite slow state
is bounded by the scalar dominator. -/
theorem embeddedSlowState_twoStepDefectRate_lt_dominator
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (n : ℕ) :
    T.twoStepCorrelationDefectRate
        (physicalYangMillsLatticeSpacingNNReal S n)
        ((V.embeddedSlowState n : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) <
      V.slowStateDominator n := by
  have hcompat :=
    V.twoStepDefectRate_le_finiteEnergy_add_excess
      n (V.finiteSlowState n) (V.finiteSlowState_norm n)
  have hslow := V.finiteSlowState_energy_lt_rate_add_spacing n
  dsimp [embeddedSlowState] at hcompat
  unfold slowStateDominator
  linarith

/-- The scalar dominators converge to the intrinsic Wilson rate limit. -/
theorem slowStateDominator_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T) :
    Tendsto V.slowStateDominator atTop (nhds C.limit) := by
  have hsum :=
    (C.rate_tendsto_limit.add S.latticeSpacing_tendsto_zero).add
      V.defectRateExcess_tendsto_zero
  simpa only [slowStateDominator, add_zero] using hsum

/-- Consequently the corrected scalar dominator converges to the same intrinsic
rate limit. -/
theorem correctedSlowStateDominator_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T) :
    Tendsto
      (fun n =>
        V.slowStateDominator n /
          (1 - 2 * S.latticeSpacing n * V.slowStateDominator n))
      atTop (nhds C.limit) := by
  simpa only [coe_physicalYangMillsLatticeSpacingNNReal] using
    tendsto_dominator_div_one_sub_two_mul_width_mul_dominator
      (h := fun n => physicalYangMillsLatticeSpacingNNReal S n)
      (M := V.slowStateDominator)
      (physicalYangMillsLatticeSpacingNNReal_coe_tendsto_zero S)
      V.slowStateDominator_tendsto_limit

/-- The denominator correction is eventually positive for the selected slow
states. -/
theorem eventually_slowStateDominator_correction_lt_one
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T) :
    ∀ᶠ n in atTop,
      2 * S.latticeSpacing n * V.slowStateDominator n < 1 := by
  simpa only [coe_physicalYangMillsLatticeSpacingNNReal] using
    eventually_two_mul_width_mul_dominator_lt_one
      (h := fun n => physicalYangMillsLatticeSpacingNNReal S n)
      (M := V.slowStateDominator)
      (physicalYangMillsLatticeSpacingNNReal_coe_tendsto_zero S)
      V.slowStateDominator_tendsto_limit

/-- The mass-free scalar two-step recovery transfer is sufficient for the
reverse variational inequality.

For sufficiently fine scales the theorem-generated finite slow states remain
nonzero after continuum graph-domain time averaging, remain vacuum-orthogonal,
and have Rayleigh quotients bounded by the corrected scalar dominators.  Passing
to the limit gives `m_phys <= C.limit` without full operator intertwining or
eigenvector convergence. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    V.correctedSlowStateDominator_tendsto_limit
  filter_upwards [V.eventually_slowStateDominator_correction_lt_one] with n hn
  let h := physicalYangMillsLatticeSpacingNNReal S n
  let psi : P.PhysicalHilbert :=
    (V.embeddedSlowState n : P.VacuumOrthogonalHilbert)
  have hh : 0 < h := physicalYangMillsLatticeSpacingNNReal_pos S n
  have hpsi : ‖psi‖ = 1 := by
    simpa [psi] using V.embeddedSlowState_norm n
  have hdM : T.twoStepCorrelationDefectRate h psi ≤ V.slowStateDominator n := by
    exact le_of_lt (V.embeddedSlowState_twoStepDefectRate_lt_dominator n)
  have hcorrection : 2 * (h : ℝ) * V.slowStateDominator n < 1 := by
    simpa [h] using hn
  have hne :
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 :=
    T.timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_dominatorCorrection_lt_one
      hSymmetric hh hpsi hdM hcorrection
  have hpsiOrth : psi ∈ P.vacuumOrthogonal := by
    exact (V.embeddedSlowState n).property
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

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer

end MathlibAnalytic
end MGAP4D

end