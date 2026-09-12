import MGAP4D.MathlibAnalytic.ContinuousLinearMapDirichletExponentialContraction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareLowerBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOptimalRayleighCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance literalBoundaryDirectSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance literalBoundaryDirectSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance literalBoundaryDirectSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance literalBoundaryDirectSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance literalBoundaryDirectSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance literalBoundaryDirectSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

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

/-- A literal shared-boundary compact-Haar Poincare inequality is a quadratic
Dirichlet coercivity estimate for the intrinsic centered one-step Wilson
operator.  This statement is deliberately independent of any separately
packaged operator-norm defect coefficient. -/
theorem centeredOneStepOperator_dirichlet_coercive_of_literal_boundary_poincare
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (mass : ℝ)
    (n : ℕ)
    (hPoincare :
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      let Fc := Pn.vacuumCenteredCarrier F
      (2 * mass * S.latticeSpacing n) *
          (∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
          S D halfExtent N hN beta hbeta Q E R hInvariant n F) :
    ∀ G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier,
      (2 * mass * S.latticeSpacing n) * ‖G‖ ^ 2 ≤
        ‖G‖ ^ 2 - ‖B.centeredOneStepOperator n G‖ ^ 2 := by
  intro G
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier (G : Pn.Carrier)
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  have hGzero := G.property
  change Pn.omega (G : Pn.Carrier).toGaugeInvariant = 0 at hGzero
  have hF0 : F0 = (G : Pn.Carrier) := by
    dsimp [F0]
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.vacuumCenteredCarrier
    rw [hGzero]
    simp
  have hp := hPoincare (G : Pn.Carrier)
  dsimp only at hp
  unfold physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree at hp
  dsimp only at hp
  have hnorm0 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
  have hnorm1 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
  change
    (2 * mass * S.latticeSpacing n) *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0 b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0 b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) -
        ∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1 b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) at hp
  rw [← hnorm0, ← hnorm1] at hp
  dsimp [F1] at hp
  rw [hF0] at hp
  have hopcoe := B.centeredOneStepOperator_apply_coe n G
  have hopnorm :
      ‖B.centeredOneStepOperator n G‖ =
        ‖R.realizableCarrierTranslation hInvariant n 1 (G : Pn.Carrier)‖ := by
    have h := congrArg norm hopcoe
    simpa using h
  rw [hopnorm]
  simpa using hp

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- Positivity data stated *only* on the literal compact-Haar OS boundary
Dirichlet form.

Unlike the earlier defect route, this certificate contains no
`physicalExcitationDirichletCoefficient`, no `defect_nonneg`, and no
`defect_lt_one`.  Its quantitative input is exactly the eventual physical
boundary Poincare inequality

`2 m a_n * boundaryVariance_n(F) <= boundaryDirichletEnergy_n(F)`.

The finite exponential contraction is derived directly from this quadratic
coercivity through `||T|| <= sqrt(1-2ma) <= exp(-ma)`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
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
  mass : ℝ
  mass_pos : 0 < mass
  eventually_boundary_poincare :
    ∀ᶠ n in atTop,
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      let Fc := Pn.vacuumCenteredCarrier F
      (2 * mass * S.latticeSpacing n) *
          (∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
          S D halfExtent N hN beta hbeta Q E R hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate

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

/-- The physical Poincare coefficient is nonnegative at every scale. -/
theorem poincareCoefficient_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ 2 * A.mass * S.latticeSpacing n := by
  exact mul_nonneg (mul_nonneg (by norm_num) A.mass_pos.le)
    (S.latticeSpacing_pos n).le

/-- Since the lattice spacing tends to zero, `2 m a_n <= 1` eventually. -/
theorem eventually_poincareCoefficient_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop, 2 * A.mass * S.latticeSpacing n ≤ 1 := by
  have hm :
      Tendsto (fun n => A.mass * S.latticeSpacing n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul S.latticeSpacing_tendsto_zero
  have hzero :
      Tendsto (fun n => 2 * A.mass * S.latticeSpacing n) atTop (nhds 0) := by
    have htwoConst :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds (2 : ℝ)) :=
      tendsto_const_nhds
    have htwo := htwoConst.mul hm
    simpa [mul_assoc] using htwo
  have hlt : ∀ᶠ n in atTop, 2 * A.mass * S.latticeSpacing n < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  exact hlt.mono fun _ h => h.le

/-- Literal boundary coercivity directly contracts the actual completed finite
physical-excitation operator exponentially.  No defect coefficient and no
logarithm occur in this proof. -/
theorem eventually_physicalExcitationOpNorm_le_exp
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ≤
        Real.exp (-A.mass * S.latticeSpacing n) := by
  filter_upwards [A.eventually_boundary_poincare,
    A.eventually_poincareCoefficient_le_one] with n hp hc
  have hcentered :
      ‖A.boundedAnalysis.centeredOneStepOperator n‖ ≤
        Real.exp (-(2 * A.mass * S.latticeSpacing n) / 2) :=
    continuousLinearMap_opNorm_le_exp_neg_half_of_dirichlet_coercive
      (A.boundedAnalysis.centeredOneStepOperator n)
      (2 * A.mass * S.latticeSpacing n)
      (A.poincareCoefficient_nonneg n)
      hc
      (A.boundedAnalysis.centeredOneStepOperator_dirichlet_coercive_of_literal_boundary_poincare
        A.mass n hp)
  have hcentered' :
      ‖A.boundedAnalysis.centeredOneStepOperator n‖ ≤
        Real.exp (-A.mass * S.latticeSpacing n) := by
    simpa only [show
      -(2 * A.mass * S.latticeSpacing n) / 2 =
        -A.mass * S.latticeSpacing n by ring] using hcentered
  rw [A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
  change ‖A.boundedAnalysis.centeredOneStepOperator n‖ ≤
    Real.exp (-A.mass * S.latticeSpacing n)
  exact hcentered'

/-- Pointwise one-step contraction on arbitrary completed physical excitation
states. -/
theorem eventually_physicalExcitationOneStep_norm_le_exp
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      ∀ psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert,
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n psi‖ ≤
          Real.exp (-A.mass * S.latticeSpacing n) * ‖psi‖ := by
  filter_upwards [A.eventually_physicalExcitationOpNorm_le_exp] with n hn
  intro psi
  calc
    ‖A.boundedAnalysis.physicalExcitationOneStepOperator n psi‖ ≤
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ * ‖psi‖ :=
      (A.boundedAnalysis.physicalExcitationOneStepOperator n).le_opNorm psi
    _ ≤ Real.exp (-A.mass * S.latticeSpacing n) * ‖psi‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg psi)

/-- The direct one-step bound iterates along the genuine floor-selected integer
Wilson trajectory, still without introducing a defect coefficient. -/
theorem eventually_floorPhysicalExcitationIterate_norm_le_exponential
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
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
          ‖psi n‖ := by
  filter_upwards [A.eventually_physicalExcitationOneStep_norm_le_exp] with n hn
  let k := physicalTemporalFloorNatStep S.latticeSpacing t n
  have hiter := norm_iterate_le_exp_pow_of_norm_le
    (fun phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
      A.boundedAnalysis.physicalExcitationOneStepOperator n phi)
    A.mass (S.latticeSpacing n) hn k (psi n)
  calc
    ‖(fun phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
        A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[k] (psi n)‖ ≤
        (Real.exp (-A.mass * S.latticeSpacing n)) ^ k * ‖psi n‖ := hiter
    _ = Real.exp (-A.mass * ((k : ℝ) * S.latticeSpacing n)) * ‖psi n‖ := by
      rw [PositiveDirichletDefectLowerBound.exp_neg_mass_spacing_pow]

/-- Scalar continuum handoff for the direct route.  The floor-time exponential
factor is controlled only by lattice-spacing convergence; no defect sequence is
present. -/
theorem floorPhysicalExcitationIterate_limit_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (psi : (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert)
    {inputNormLimit evolvedNormLimit : ℝ}
    (hInput : Tendsto (fun n => ‖psi n‖) atTop (nhds inputNormLimit))
    (hEvolved :
      Tendsto
        (fun n =>
          ‖(fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n] (psi n)‖)
        atTop (nhds evolvedNormLimit)) :
    evolvedNormLimit ≤ Real.exp (-A.mass * (t : ℝ)) * inputNormLimit := by
  apply le_of_tendsto_of_tendsto hEvolved
    ((physicalTemporalFloorExponentialFactor_tendsto
      S.latticeSpacing S.latticeSpacing_pos S.latticeSpacing_tendsto_zero A.mass t).mul hInput)
  exact A.eventually_floorPhysicalExcitationIterate_norm_le_exponential t psi

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate

/-- Cross-scale common-carrier transfer for the direct literal-boundary route.
The finite evolution is the genuine floor-selected completed Wilson excitation
operator, and the only model-specific continuum input is norm convergence of
approximating states and their evolved norms. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
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
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) where
  approximateExcitation :
    (n : ℕ) → P.VacuumOrthogonalHilbert →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert
  approximate_norm_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto (fun n => ‖approximateExcitation n psi‖) atTop (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n =>
          ‖(fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n]
              (approximateExcitation n psi)‖)
        atTop
        (nhds ‖T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert)‖)

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer

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
    {A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- The genuine finite floor-time Wilson contraction passes to the continuum OS
semigroup directly from literal boundary Poincare coercivity. -/
theorem continuumExcitation_norm_le_exp
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (t : NNReal)
    (psi : P.VacuumOrthogonalHilbert) :
    ‖T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert)‖ ≤
      Real.exp (-A.mass * (t : ℝ)) * ‖psi‖ := by
  exact
    A.floorPhysicalExcitationIterate_limit_norm_le
      t
      (fun n => G.approximateExcitation n psi)
      (G.approximate_norm_tendsto psi)
      (G.evolved_norm_tendsto t psi)

/-- Package the direct exponential continuum estimate as the canonical vacuum
semigroup gap slope. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T) :
    T.VacuumSemigroupGapSlope where
  mass := A.mass
  mass_pos := A.mass_pos
  decayFactor := fun t => Real.exp (-A.mass * (t : ℝ))
  slope_tendsto := tendsto_nnreal_inv_mul_one_sub_exp_neg_mul A.mass
  decay := by
    intro t psi hpsi
    have hmem : psi ∈ P.vacuumOrthogonal := by
      rw [P.mem_vacuumOrthogonal_iff, real_inner_comm]
      exact hpsi
    let psiOrth : P.VacuumOrthogonalHilbert := ⟨psi, hmem⟩
    have h := G.continuumExcitation_norm_le_exp t psiOrth
    simpa [psiOrth] using h

/-- The actual graph-closed physical Hamiltonian therefore satisfies the
Rayleigh lower bound generated directly by literal boundary coercivity. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    A.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope hP psi hpsi

/-- The direct literal-boundary mass is an admissible variational coercivity
constant for the actual physical Yang--Mills Hamiltonian. -/
theorem mass_mem_physicalYangMillsRayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized) :
    A.mass ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi _hpsiNonzero horthogonal
  exact G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq hP psi horthogonal

/-- Consequently the direct literal-boundary mass lies below the intrinsic
variational physical Yang--Mills mass. -/
theorem mass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    A.mass ≤ T.physicalYangMillsMass :=
  T.rayleighLowerBound_le_physicalYangMillsMass
    W (G.mass_mem_physicalYangMillsRayleighLowerBoundSet hP)

/-- If the literal Wilson boundary analysis proves that this mass is the
largest admissible physical Rayleigh coercivity constant, the physical
Yang--Mills mass is theorem-generated as exactly this value. -/
theorem physicalYangMillsMass_eq_of_isGreatest
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hGreatest : IsGreatest T.physicalYangMillsRayleighLowerBoundSet A.mass) :
    T.physicalYangMillsMass = A.mass :=
  T.physicalYangMillsMass_eq_of_isGreatest_rayleighLowerBoundSet W hGreatest

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end