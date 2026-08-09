import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateToPhysicalMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryPoincareOptimalMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance poincareIntrinsicRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance poincareIntrinsicRateSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance poincareIntrinsicRateSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance poincareIntrinsicRateSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance poincareIntrinsicRateSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance poincareIntrinsicRateSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

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
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The intrinsic logarithmic rate of every finite centered Wilson contraction
is nonnegative. -/
theorem intrinsicCenteredMassRate_nonneg
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
      C.boundedAnalysis n := by
  unfold physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
  have hlog : Real.log (C.boundedAnalysis.centeredTransferFactor n) ≤ 0 :=
    Real.log_nonpos (C.transferFactor_pos n).le (C.transferFactor_le_one n)
  exact div_nonneg (neg_nonneg.mpr hlog) (S.latticeSpacing_pos n).le

/-- Any positive intrinsic literal-boundary-admissible Wilson mass gives the
defect-free direct finite gap certificate on the same actual bounded one-step
analysis. -/
noncomputable def toDirectGapCertificateOfAdmissibleMass
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := C.boundedAnalysis
  mass := m
  mass_pos := hm_pos
  eventually_boundary_poincare := hm.2

/-- A positive literal Wilson Poincare mass is eventually below the exact
logarithmic mass rate of the actual finite excitation transfer operator.

The proof takes logarithms of the defect-free direct bound

`||T_n^exc|| <= exp(-m a_n)`

and divides by the positive lattice spacing. -/
theorem positive_admissibleMass_eventually_le_intrinsicCenteredMassRate
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    ∀ᶠ n in atTop,
      m ≤ physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n := by
  let A := C.toDirectGapCertificateOfAdmissibleMass m hm_pos hm
  filter_upwards [A.eventually_physicalExcitationOpNorm_le_exp] with n hn
  have hfactor :
      C.boundedAnalysis.centeredTransferFactor n ≤
        Real.exp (-m * S.latticeSpacing n) := by
    simpa only [
      C.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
      using hn
  have hlog :
      Real.log (C.boundedAnalysis.centeredTransferFactor n) ≤
        -m * S.latticeSpacing n :=
    (Real.log_le_iff_le_exp (C.transferFactor_pos n)).2 hfactor
  unfold physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
  apply (le_div_iff₀ (S.latticeSpacing_pos n)).2
  linarith

/-- Every nonnegative literal-Wilson admissible mass, including zero, is
eventually bounded above by the intrinsic finite spectral rate. -/
theorem admissibleMass_eventually_le_intrinsicCenteredMassRate
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    {m : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    ∀ᶠ n in atTop,
      m ≤ physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n := by
  by_cases hzero : m = 0
  · subst m
    exact Filter.Eventually.of_forall fun n => C.intrinsicCenteredMassRate_nonneg n
  · have hm_pos : 0 < m := lt_of_le_of_ne hm.1 (Ne.symm hzero)
    exact C.positive_admissibleMass_eventually_le_intrinsicCenteredMassRate
      m hm_pos hm

/-- Passing to the intrinsic rate limit, every literal-Wilson admissible mass is
bounded above by the continuum rate reconstructed from the actual finite
excitation operator norms. -/
theorem admissibleMass_le_limit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    {m : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    m ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds C.rate_tendsto_limit
  exact C.admissibleMass_eventually_le_intrinsicCenteredMassRate hm

/-- Hence the intrinsic optimal Wilson boundary Poincare mass is bounded by the
exact continuum rate obtained from the finite transfer-operator spectrum. -/
theorem boundaryPoincareOptimalMass_le_limit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant ≤ C.limit := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
  exact csSup_le hNonempty fun m hm => C.admissibleMass_le_limit hm

/-- One positive literal-Wilson admissible mass already proves strict positivity
of the derived intrinsic continuum spectral rate. -/
theorem limit_pos_of_positive_admissibleMass
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    0 < C.limit :=
  lt_of_lt_of_le hm_pos (C.admissibleMass_le_limit hm)

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- If genuine reverse spectral recovery identifies the intrinsic Wilson
Poincare optimum with the variational physical mass, then the independently
derived exact transfer-rate limit is forced to be that same physical mass.

The proof is the intrinsic sandwich

`m_W^* <= g_infty <= m_YM`

plus `m_W^* = m_YM`.  No numerical value is inserted. -/
theorem limit_eq_physicalYangMillsMass_of_boundaryOptimal_eq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (hOptimalEq :
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant =
        T.physicalYangMillsMass) :
    C.limit = T.physicalYangMillsMass := by
  have hlimit_pos := C.limit_pos_of_positive_admissibleMass m hm_pos hm
  have hupper := G.limit_le_physicalYangMillsMass hlimit_pos hP W
  have hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty :=
    ⟨m, hm⟩
  have hoptle := C.boundaryPoincareOptimalMass_le_limit hNonempty
  have hlower : T.physicalYangMillsMass ≤ C.limit := by
    rw [← hOptimalEq]
    exact hoptle
  exact le_antisymm hupper hlower

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end