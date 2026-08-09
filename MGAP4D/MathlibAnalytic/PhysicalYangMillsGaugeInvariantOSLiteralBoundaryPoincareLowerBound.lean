import MGAP4D.MathlibAnalytic.ContinuousLinearMapDirichletDefectOpNorm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletLowerBoundGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance literalBoundaryPoincareSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance literalBoundaryPoincareSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance literalBoundaryPoincareSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance literalBoundaryPoincareSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance literalBoundaryPoincareSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance literalBoundaryPoincareSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Vacuum centering acts identically on an already expectation-zero carrier
point. -/
theorem vacuumCenteredCarrier_coe_centeredCarrier
    (P : D.OSPreHilbertData)
    (F : P.CenteredCarrier) :
    P.vacuumCenteredCarrier (F : P.Carrier) = (F : P.Carrier) := by
  unfold vacuumCenteredCarrier
  rw [F.property]
  simp

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- The hard finite Wilson mass-gap input stated on the literal compact-Haar
shared-boundary Dirichlet form rather than on an operator norm.

For sufficiently fine scales, every vacuum-centered finite OS carrier obeys

`2 m a_n * boundaryVariance_n(F) <= boundaryDirichletEnergy_n(F)`.

The coefficient contains no exact mass value and no auxiliary transfer factor.
The two defect-regularity fields are kept explicit: this package does not hide
a separate proof that the actual finite excitation operator is a nonzero
contraction. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate

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

/-- The physical Poincare coefficient `2 m a_n` is nonnegative at every scale. -/
theorem poincareCoefficient_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ 2 * A.mass * S.latticeSpacing n := by
  positivity

/-- Since `a_n -> 0`, the physical Poincare coefficient is eventually at most
one.  This is generated by the continuum lattice scaling, not assumed. -/
theorem eventually_poincareCoefficient_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop, 2 * A.mass * S.latticeSpacing n ≤ 1 := by
  have hzero :
      Tendsto (fun n => 2 * A.mass * S.latticeSpacing n) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul S.latticeSpacing_tendsto_zero).const_mul (2 : ℝ)
  exact (tendsto_order.1 hzero).2 1 zero_lt_one |>.mono fun _ h => h.le

/-- A literal boundary Poincare inequality at one scale is exactly a quadratic
Dirichlet coercivity estimate for the intrinsic centered one-step Wilson
operator. -/
theorem centeredOneStepOperator_dirichlet_coercive_of_boundary_poincare
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (hPoincare :
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      let Fc := Pn.vacuumCenteredCarrier F
      (2 * A.mass * S.latticeSpacing n) *
          (∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
          S D halfExtent N hN beta hbeta Q E R hInvariant n F) :
    ∀ G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier,
      (2 * A.mass * S.latticeSpacing n) * ‖G‖ ^ 2 ≤
        ‖G‖ ^ 2 - ‖A.boundedAnalysis.centeredOneStepOperator n G‖ ^ 2 := by
  intro G
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hcenter :
      Pn.vacuumCenteredCarrier (G : Pn.Carrier) = (G : Pn.Carrier) :=
    Pn.vacuumCenteredCarrier_coe_centeredCarrier G
  have hp := hPoincare (G : Pn.Carrier)
  dsimp only at hp
  rw [hcenter] at hp
  have hnorm :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (G : Pn.Carrier)
  have henergy :=
    physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy_massFree
      R hInvariant n (G : Pn.Carrier)
  dsimp only at henergy
  rw [hcenter] at henergy
  have hdouble :=
    R.realizableCarrierTranslation_one_norm_sq_eq_inner_two_massFree
      hInvariant n (G : Pn.Carrier)
  rw [← hnorm, ← henergy, ← hdouble] at hp
  rw [real_inner_self_eq_norm_sq] at hp
  change
    (2 * A.mass * S.latticeSpacing n) * ‖G‖ ^ 2 ≤
      ‖G‖ ^ 2 - ‖A.boundedAnalysis.centeredOneStepOperator n G‖ ^ 2
  simpa only [A.boundedAnalysis.centeredOneStepOperator_apply_coe] using hp

/-- Therefore the literal compact-Haar Poincare coefficient lower-bounds the
intrinsic physical excitation Dirichlet defect. -/
theorem physicalExcitationDirichletCoefficient_lower_of_boundary_poincare
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (hCoeff : 2 * A.mass * S.latticeSpacing n ≤ 1)
    (hPoincare :
      ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      let Fc := Pn.vacuumCenteredCarrier F
      (2 * A.mass * S.latticeSpacing n) *
          (∫ b,
            ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
              S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
            ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
        physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
          S D halfExtent N hN beta hbeta Q E R hInvariant n F) :
    2 * A.mass * S.latticeSpacing n ≤
      A.boundedAnalysis.physicalExcitationDirichletCoefficient n := by
  have hcentered :
      2 * A.mass * S.latticeSpacing n ≤
        1 - ‖A.boundedAnalysis.centeredOneStepOperator n‖ ^ 2 :=
    continuousLinearMap_le_one_sub_opNorm_sq_of_dirichlet_coercive
      (A.boundedAnalysis.centeredOneStepOperator n)
      (2 * A.mass * S.latticeSpacing n)
      (A.poincareCoefficient_nonneg n)
      hCoeff
      (A.centeredOneStepOperator_dirichlet_coercive_of_boundary_poincare n hPoincare)
  rw [A.boundedAnalysis.physicalExcitationDirichletCoefficient_eq_centeredTransferFactor]
  change
    2 * A.mass * S.latticeSpacing n ≤
      1 - ‖A.boundedAnalysis.centeredOneStepOperator n‖ ^ 2
  exact hcentered

/-- The eventual literal boundary Poincare inequality theorem-generates the
operator-defect lower bound required by #1525. -/
theorem eventually_physicalExcitationDirichletCoefficient_lower
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      2 * A.mass * S.latticeSpacing n ≤
        A.boundedAnalysis.physicalExcitationDirichletCoefficient n := by
  filter_upwards [A.eventually_boundary_poincare,
    A.eventually_poincareCoefficient_le_one] with n hp hc
  exact A.physicalExcitationDirichletCoefficient_lower_of_boundary_poincare n hc hp

/-- Thus literal compact-Haar boundary coercivity packages directly into the
actual physical-excitation mass-gap lower-bound route. -/
noncomputable def toPhysicalExcitationDirichletLowerBoundCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := A.mass
  mass_pos := A.mass_pos
  eventually_defect_lower := A.eventually_physicalExcitationDirichletCoefficient_lower

/-- Consequently the literal Wilson boundary Poincare lower bound generates the
same continuum floor-time exponential decay as #1525, without assuming an
operator-norm defect lower bound separately. -/
theorem floorPhysicalExcitationIterate_limit_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate
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
    evolvedNormLimit ≤ Real.exp (-A.mass * (t : ℝ)) * inputNormLimit :=
  A.toPhysicalExcitationDirichletLowerBoundCertificate.floorPhysicalExcitationIterate_limit_norm_le
    t psi hInput hEvolved

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareLowerBoundCertificate

end MathlibAnalytic
end MGAP4D

end