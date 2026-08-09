import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletLowerBoundGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationBoundaryDirichletCoefficient
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A generic operator-norm lemma: if every vector loses at least a fraction
`c` of its squared norm under a continuous linear map, then `c` is a lower
bound for the squared operator-norm defect.

The proof uses Mathlib's canonical `ContinuousLinearMap.opNorm_le_bound` rather
than approximate norm-attaining vectors. -/
theorem continuousLinearMap_dirichletCoefficient_le_sqNormDefect
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V)
    (c : ℝ)
    (hc : c ≤ 1)
    (hDirichlet : ∀ x : V,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    c ≤ 1 - ‖T‖ ^ 2 := by
  have hOneMinus : 0 ≤ 1 - c := sub_nonneg.mpr hc
  have hOp : ‖T‖ ≤ Real.sqrt (1 - c) := by
    apply ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _)
    intro x
    have hx := hDirichlet x
    have hroot : (Real.sqrt (1 - c)) ^ 2 = 1 - c :=
      Real.sq_sqrt hOneMinus
    have hsquare :
        ‖T x‖ ^ 2 ≤ (Real.sqrt (1 - c) * ‖x‖) ^ 2 := by
      rw [mul_pow, hroot]
      nlinarith
    nlinarith [norm_nonneg (T x), norm_nonneg x,
      Real.sqrt_nonneg (1 - c),
      mul_nonneg (Real.sqrt_nonneg (1 - c)) (norm_nonneg x)]
  have hroot : (Real.sqrt (1 - c)) ^ 2 = 1 - c :=
    Real.sq_sqrt hOneMinus
  have hOpSq : ‖T‖ ^ 2 ≤ (Real.sqrt (1 - c)) ^ 2 := by
    nlinarith [norm_nonneg T, Real.sqrt_nonneg (1 - c)]
  rw [hroot] at hOpSq
  linarith

local instance boundaryPoincareDefectSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPoincareDefectSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPoincareDefectSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryPoincareDefectSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryPoincareDefectSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryPoincareDefectSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Literal compact-Haar boundary variance of a point already lying in the
actual finite Wilson centered carrier sector. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
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
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) : ℝ :=
  ∫ b,
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) b‖ ^ 2
    ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

/-- Literal one-step compact-Haar boundary Dirichlet energy on the actual
centered carrier sector.  It is the difference between the boundary variance
before and after one genuine integer Wilson time step. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) : ℝ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F1 : Pn.CenteredCarrier :=
    ⟨R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier),
      R.realizableCarrierTranslation_mem_centeredCarrierSubmodule
        hInvariant n 1 F⟩
  exact
    physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
        S D halfExtent N hN beta hbeta Q hInvariant n F -
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
        S D halfExtent N hN beta hbeta Q hInvariant n F1

/-- On the centered carrier, the literal compact-Haar boundary variance is
exactly the carrier squared norm. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryVariance_eq_norm_sq
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
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
      S D halfExtent N hN beta hbeta Q hInvariant n F = ‖F‖ ^ 2 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have h :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (F : Pn.Carrier)
  unfold physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
  simpa only using h.symm

/-- The literal centered-sector boundary energy is exactly the one-step squared
norm loss of the actual Wilson centered carrier translation. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryDirichletEnergy_eq_norm_sq_sub
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
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
        S D halfExtent N hN beta hbeta Q E R hInvariant n F =
      ‖F‖ ^ 2 -
        ‖R.realizableCarrierTranslation hInvariant n 1
          (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)‖ ^ 2 := by
  unfold physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
  rw [physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryVariance_eq_norm_sq,
    physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryVariance_eq_norm_sq]
  rfl

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

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

/-- Any literal compact-Haar Poincare coefficient on the actual centered Wilson
boundary sector is bounded above by the intrinsic physical-excitation
Dirichlet coefficient `1 - ||T_n^exc||^2`.

This is the reverse direction missing from the earlier boundary-Poincare API:
the boundary inequality now controls the actual completed excitation operator
norm, rather than merely being generated from that norm. -/
theorem physicalExcitationDirichletCoefficient_ge_of_centeredBoundaryPoincare
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (c : ℝ)
    (hc : c ≤ 1)
    (hPoincare :
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier,
        c *
            physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
              S D halfExtent N hN beta hbeta Q hInvariant n F ≤
          physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
            S D halfExtent N hN beta hbeta Q E R hInvariant n F) :
    c ≤ A.physicalExcitationDirichletCoefficient n := by
  rw [A.physicalExcitationDirichletCoefficient_eq_centeredTransferFactor]
  change c ≤ 1 - ‖A.centeredOneStepOperator n‖ ^ 2
  apply continuousLinearMap_dirichletCoefficient_le_sqNormDefect
    (A.centeredOneStepOperator n) c hc
  intro F
  have h := hPoincare F
  rw [physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryVariance_eq_norm_sq,
    physical_yang_mills_evenPeriodicWilsonOS_centeredSectorBoundaryDirichletEnergy_eq_norm_sq_sub]
    at h
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hnorm :
      ‖A.centeredOneStepOperator n F‖ =
        ‖R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier)‖ := by
    change
      ‖((A.centeredOneStepOperator n F : Pn.CenteredCarrier) : Pn.Carrier)‖ = _
    rw [A.centeredOneStepOperator_apply_coe]
  rw [hnorm]
  exact h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- A genuinely boundary-local positive-gap input.

The quantitative hypothesis is no longer a lower bound on an operator norm
defect.  It is an eventual literal compact-Haar Poincare inequality on every
centered finite Wilson boundary moment:

`2 m a_n * boundaryVariance(F) <= boundaryDirichletEnergy(F)`.

The existing finite conditions `0 <= delta_n < 1` are kept explicit because
they ensure the positive defect-derived transfer factor used by #1525. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
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
  defect_nonneg : ∀ n,
    0 ≤ boundedAnalysis.physicalExcitationDirichletCoefficient n
  defect_lt_one : ∀ n,
    boundedAnalysis.physicalExcitationDirichletCoefficient n < 1
  mass : ℝ
  mass_pos : 0 < mass
  eventually_boundary_poincare :
    ∀ᶠ n in atTop,
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier,
        (2 * mass * S.latticeSpacing n) *
            physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryVariance
              S D halfExtent N hN beta hbeta Q hInvariant n F ≤
          physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredSectorBoundaryDirichletEnergy
            S D halfExtent N hN beta hbeta Q E R hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate

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

/-- Since `a_n -> 0`, every fixed positive mass coefficient `2 m a_n` is at
most one eventually.  Thus the square-root bound required by the generic
operator-norm lemma is generated, not assumed. -/
theorem eventually_two_mul_mass_mul_latticeSpacing_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop, 2 * A.mass * S.latticeSpacing n ≤ 1 := by
  have hscaled :
      Tendsto (fun n => (2 * A.mass) * S.latticeSpacing n)
        atTop (nhds 0) := by
    simpa using S.latticeSpacing_tendsto_zero.const_mul (2 * A.mass)
  have hlt :
      ∀ᶠ n in atTop, (2 * A.mass) * S.latticeSpacing n < 1 :=
    (tendsto_order.1 hscaled).2 1 zero_lt_one
  filter_upwards [hlt] with n hn
  simpa [mul_assoc] using hn.le

/-- The literal boundary Poincare inequality theorem-generates the actual
physical-excitation Dirichlet-defect lower bound consumed by #1525. -/
theorem eventually_physicalExcitationDirichletCoefficient_lower
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      2 * A.mass * S.latticeSpacing n ≤
        A.boundedAnalysis.physicalExcitationDirichletCoefficient n := by
  filter_upwards [A.eventually_boundary_poincare,
    A.eventually_two_mul_mass_mul_latticeSpacing_le_one] with n hPoincare hle
  exact A.boundedAnalysis.physicalExcitationDirichletCoefficient_ge_of_centeredBoundaryPoincare
    n (2 * A.mass * S.latticeSpacing n) hle hPoincare

/-- Forget the literal boundary presentation after deriving the operator-norm
defect inequality.  Downstream exponential decay is then entirely generated by
#1525. -/
noncomputable def toPhysicalExcitationDirichletLowerBoundCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := A.mass
  mass_pos := A.mass_pos
  eventually_defect_lower := A.eventually_physicalExcitationDirichletCoefficient_lower

/-- Therefore a literal compact-Haar boundary Poincare lower bound directly
produces the eventual exponential one-step contraction of the actual completed
finite physical-excitation operator. -/
theorem eventually_physicalExcitationOpNorm_le_exp
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ≤
        Real.exp (-A.mass * S.latticeSpacing n) :=
  A.toPhysicalExcitationDirichletLowerBoundCertificate.eventually_physicalExcitationOpNorm_le_exp

/-- The same literal boundary input controls every genuine floor-selected
finite physical-excitation iterate. -/
theorem eventually_floorPhysicalExcitationIterate_norm_le_exponential
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
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
            (-A.mass *
              ((physicalTemporalFloorNatStep S.latticeSpacing t n : ℝ) *
                S.latticeSpacing n)) *
          ‖psi n‖ :=
  A.toPhysicalExcitationDirichletLowerBoundCertificate.eventually_floorPhysicalExcitationIterate_norm_le_exponential
    t psi

end PhysicalYangMillsEvenPeriodicWilsonOSCenteredBoundaryPoincareMassLowerBoundCertificate

end MathlibAnalytic
end MGAP4D

end