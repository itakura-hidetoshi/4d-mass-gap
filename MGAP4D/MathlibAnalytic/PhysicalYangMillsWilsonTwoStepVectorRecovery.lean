import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonScalarTwoStepReverseMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateNonnegativeRecoveryClosure
import MGAP4D.MathlibAnalytic.ContinuousLinearMapIsometricSubmoduleRange
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance vectorRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance vectorRecoverySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vectorRecoverySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vectorRecoverySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vectorRecoverySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vectorRecoverySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A mass-free finite-to-continuum recovery condition stated at the vector
level rather than directly at the scalar Rayleigh level.

For each finite Wilson excitation vector `phi`, compare the continuum two-step
evolution of its embedded vector with the embedding of the actual finite
completed two-step excitation operator.  The residual is required to be
`2 a_n * delta_n` with `delta_n -> 0`.

This is stronger than the scalar compatibility used by #1575, but it is a much
more geometric target for a projective/common-carrier construction.  It stores
no physical mass, spectral vector, compactness certificate, or target exact
number. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer
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
  vectorDefectExcess : ℕ → ℝ
  vectorDefectExcess_tendsto_zero : Tendsto vectorDefectExcess atTop (nhds 0)
  twoStepVectorDefect_le :
    ∀ n phi, ‖phi‖ = 1 →
      let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
      let eta := excitationEmbed n ((K ∘L K) phi)
      let psi := excitationEmbed n phi
      ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator
            (physicalYangMillsLatticeSpacingNNReal S n +
              physicalYangMillsLatticeSpacingNNReal S n)
            (psi : P.PhysicalHilbert)‖ ≤
        2 * S.latticeSpacing n * vectorDefectExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer

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

/-- A vector `o(a_n)` recovery transfer canonically implies the scalar
compatibility used by the reverse Rayleigh theorem.

The only analytic input is real Cauchy--Schwarz.  Isometry identifies the
finite quadratic term with the quadratic term of its continuum embedding, and
the vector residual controls the difference between the two scalar two-step
correlations. -/
noncomputable def toScalarTwoStepRecoveryTransfer
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer C P T) :
    PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateScalarTwoStepRecoveryTransfer C P T where
  excitationEmbed := V.excitationEmbed
  excitationEmbed_norm := V.excitationEmbed_norm
  defectRateExcess := V.vectorDefectExcess
  defectRateExcess_tendsto_zero := V.vectorDefectExcess_tendsto_zero
  twoStepDefectRate_le_finiteEnergy_add_excess := by
    intro n phi hphi
    let h := physicalYangMillsLatticeSpacingNNReal S n
    let A := C.boundedAnalysis.physicalExcitationOneStepOperator n
    let etaFinite := (A ∘L A) phi
    let psiOrth : P.VacuumOrthogonalHilbert := V.excitationEmbed n phi
    let etaOrth : P.VacuumOrthogonalHilbert := V.excitationEmbed n etaFinite
    let psi : P.PhysicalHilbert := (psiOrth : P.PhysicalHilbert)
    let eta : P.PhysicalHilbert := (etaOrth : P.PhysicalHilbert)
    have hdenpos : 0 < 2 * S.latticeSpacing n := by
      nlinarith [S.latticeSpacing_pos n]
    have hpsiNorm : ‖psi‖ = 1 := by
      change ‖V.excitationEmbed n phi‖ = 1
      rw [V.excitationEmbed_norm n phi, hphi]
    have hinnerIso0 :=
      ContinuousLinearMap.inner_map_map_of_norm_map
        (V.excitationEmbed n) (fun x => V.excitationEmbed_norm n x)
        etaFinite phi
    have hinnerIso : inner ℝ eta psi = inner ℝ etaFinite phi := by
      simpa [eta, psi, etaOrth, psiOrth] using hinnerIso0
    have hvec0 := V.twoStepVectorDefect_le n phi hphi
    have hvec :
        ‖eta - T.toPhysicalSemigroup.operator (h + h) psi‖ ≤
          2 * S.latticeSpacing n * V.vectorDefectExcess n := by
      simpa [h, eta, etaOrth, etaFinite, A, psi, psiOrth] using hvec0
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
      rw [hpsiNorm]
      norm_num
      linarith
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
        field_simp [ne_of_gt hdenpos]
        ring

/-- The vector recovery condition already implies the reverse variational mass
inequality through the scalar transfer constructed above. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer C P T)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit :=
  V.toScalarTwoStepRecoveryTransfer.physicalYangMillsMass_le_limit hSymmetric

/-- The vector recovery condition also supplies at least one genuine nonzero
vacuum-orthogonal graph-domain excitation state.  This witness is extracted
from the same sufficiently fine time-averaged slow state used in the reverse
inequality. -/
theorem excitationDomainWitness_nonempty
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer C P T)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    Nonempty T.PhysicalYangMillsExcitationDomainWitness := by
  let W := V.toScalarTwoStepRecoveryTransfer
  have hexists : ∃ n,
      2 * S.latticeSpacing n * W.slowStateDominator n < 1 :=
    W.eventually_slowStateDominator_correction_lt_one.exists
  rcases hexists with ⟨n, hn⟩
  let h := physicalYangMillsLatticeSpacingNNReal S n
  let psi : P.PhysicalHilbert :=
    (W.embeddedSlowState n : P.VacuumOrthogonalHilbert)
  have hh : 0 < h := physicalYangMillsLatticeSpacingNNReal_pos S n
  have hpsi : ‖psi‖ = 1 := by
    simpa [psi] using W.embeddedSlowState_norm n
  have hdM : T.twoStepCorrelationDefectRate h psi ≤ W.slowStateDominator n := by
    exact le_of_lt (W.embeddedSlowState_twoStepDefectRate_lt_dominator n)
  have hcorrection : 2 * (h : ℝ) * W.slowStateDominator n < 1 := by
    simpa [h] using hn
  have hne :
      (T.timeAverageClosedRightHamiltonianDomain h psi : P.PhysicalHilbert) ≠ 0 :=
    T.timeAverageClosedRightHamiltonianDomain_ne_zero_of_unit_and_dominatorCorrection_lt_one
      hSymmetric hh hpsi hdM hcorrection
  have hpsiOrth : psi ∈ P.vacuumOrthogonal := by
    exact (W.embeddedSlowState n).property
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

/-- Conditional equality of the intrinsic Wilson rate limit and the physical
Yang--Mills variational mass from two independent mass-free directions:

* the existing continuum-to-finite common-carrier theorem gives
  `C.limit <= m_phys`;
* the vector `o(a_n)` finite-to-continuum recovery gives
  `m_phys <= C.limit`.

No positive mass certificate and no abstract spectral eigenvector convergence
is an input. -/
theorem limit_eq_physicalYangMillsMass
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer C P T)
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

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer

end MathlibAnalytic
end MGAP4D

end