import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScaling3320
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletLowerBoundGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PositiveDirichletDefectScaling

variable {latticeSpacing defect : ℕ → ℝ}

/-- Exact first-order Dirichlet-defect scaling at mass `M` automatically gives
every strictly subcritical one-sided mass lower bound.

If

`defect n / latticeSpacing n -> 2 * M`

and `0 < m < M`, then eventually

`2 * m * latticeSpacing n <= defect n`.

This is an order-theoretic consequence of the exact limit; no logarithm,
Taylor expansion, or extra spectral input is used. -/
theorem eventually_defect_lower_of_lt_mass
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (m : ℝ)
    (hm_lt : m < A.mass) :
    ∀ᶠ n in atTop,
      2 * m * latticeSpacing n ≤ defect n := by
  have hTwoMass : 2 * m < 2 * A.mass := by
    linarith
  have hEventuallyRatio :
      ∀ᶠ n in atTop,
        2 * m < defect n / latticeSpacing n :=
    (tendsto_order.1 A.defectRate_tendsto).1 (2 * m) hTwoMass
  filter_upwards [hEventuallyRatio] with n hn
  exact ((lt_div_iff₀ (A.latticeSpacing_pos n)).mp hn).le

/-- Forget exact first-order scaling while retaining any chosen positive
subcritical mass.  Thus the exact-scaling route canonically contains the
one-sided positive-gap route. -/
noncomputable def toLowerBoundOfLtMass
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < A.mass) :
    PositiveDirichletDefectLowerBound latticeSpacing defect where
  latticeSpacing_pos := A.latticeSpacing_pos
  latticeSpacing_tendsto_zero := A.latticeSpacing_tendsto_zero
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := m
  mass_pos := hm_pos
  eventually_defect_lower := A.eventually_defect_lower_of_lt_mass m hm_lt

end PositiveDirichletDefectScaling

local instance dirichletScalingLowerSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance dirichletScalingLowerSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance dirichletScalingLowerSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance dirichletScalingLowerSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance dirichletScalingLowerSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance dirichletScalingLowerSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate

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

/-- An exact actual-Wilson Dirichlet scaling certificate at mass `M`
canonically produces the actual-Wilson one-sided lower-bound certificate at
every positive `m < M`. -/
noncomputable def toPhysicalExcitationDirichletLowerBoundCertificateOfLtMass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < A.mass) :
    PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := m
  mass_pos := hm_pos
  eventually_defect_lower :=
    (A.toPositiveDirichletDefectScaling.toLowerBoundOfLtMass m hm_pos hm_lt).eventually_defect_lower

/-- Hence every positive subcritical mass immediately gives the actual finite
physical-excitation one-step exponential operator-norm bound. -/
theorem eventually_physicalExcitationOpNorm_le_exp_of_lt_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < A.mass) :
    ∀ᶠ n in atTop,
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ≤
        Real.exp (-m * S.latticeSpacing n) := by
  exact
    (A.toPhysicalExcitationDirichletLowerBoundCertificateOfLtMass
      m hm_pos hm_lt).eventually_physicalExcitationOpNorm_le_exp

end PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate

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

/-- The exact normalized `33/20` Dirichlet-scaling route contains the one-sided
positive-gap route at every strictly subcritical positive mass
`0 < m < 33/20`.

The endpoint `33/20` itself is obtained by the exact limit theorem in #1523;
convergence alone does not assert a one-sided inequality exactly at the limit. -/
noncomputable def toPhysicalExcitationDirichletLowerBoundCertificateOfLt3320
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < (33 : ℝ) / 20) :
    PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant := by
  let G := A.toPhysicalExcitationDirichletScalingCertificate
  have hm_lt_G : m < G.mass := by
    dsimp [G, toPhysicalExcitationDirichletScalingCertificate]
    exact hm_lt
  exact G.toPhysicalExcitationDirichletLowerBoundCertificateOfLtMass m hm_pos hm_lt_G

/-- Every positive `m < 33/20` is therefore an eventual actual finite Wilson
one-step exponential contraction rate, generated solely from the exact physical
Dirichlet slope. -/
theorem eventually_physicalExcitationOpNorm_le_exp_of_lt_33_over_20
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < (33 : ℝ) / 20) :
    ∀ᶠ n in atTop,
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ≤
        Real.exp (-m * S.latticeSpacing n) := by
  exact
    (A.toPhysicalExcitationDirichletLowerBoundCertificateOfLt3320
      m hm_pos hm_lt).eventually_physicalExcitationOpNorm_le_exp

/-- The exact `33/20` slope consequently yields the full genuine floor-time
finite-excitation norm estimate at every positive subcritical rate. -/
theorem eventually_floorPhysicalExcitationIterate_norm_le_exponential_of_lt_33_over_20
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm_lt : m < (33 : ℝ) / 20)
    (t : NNReal)
    (psi : (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ∀ᶠ n in atTop,
      ‖(fun phi :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
          A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
            physicalTemporalFloorNatStep S.latticeSpacing t n] (psi n)‖ ≤
        Real.exp
            (-m *
              ((physicalTemporalFloorNatStep S.latticeSpacing t n : ℝ) *
                S.latticeSpacing n)) *
          ‖psi n‖ := by
  exact
    (A.toPhysicalExcitationDirichletLowerBoundCertificateOfLt3320
      m hm_pos hm_lt).eventually_floorPhysicalExcitationIterate_norm_le_exponential t psi

end PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate

end MathlibAnalytic
end MGAP4D

end