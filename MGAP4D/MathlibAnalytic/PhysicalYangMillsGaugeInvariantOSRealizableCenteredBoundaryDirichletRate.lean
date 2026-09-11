import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredOneStepOperatorRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableBoundaryL2DerivedOneStepBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAdditiveSymmetricAction
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableCenteredBoundaryDirichletSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableCenteredBoundaryDirichletSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableCenteredBoundaryDirichletSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableCenteredBoundaryDirichletSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableCenteredBoundaryDirichletSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableCenteredBoundaryDirichletSpecialUnitaryBorelSpace
    (N : ℕ) :
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

/-- The actual realizable finite Wilson carrier translations, viewed only as a
symmetric additive action.  This construction contains no mass value and no
quantitative decay hypothesis. -/
noncomputable def toMassFreeAdditiveSymmetricAction
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.AdditiveSymmetricAction ℕ := by
  dsimp only
  exact {
    translate := R.realizableCarrierTranslation hInvariant n
    translate_zero := R.realizableCarrierTranslation_zero hInvariant n
    translate_add := by
      intro k l F
      have h := R.realizableCarrierTranslation_add hInvariant n l k F
      simpa [Nat.add_comm] using h
    inner_symmetric := by
      intro k F G
      exact R.realizableCarrierTranslation_inner_symmetric hInvariant n k F G
  }

@[simp] theorem toMassFreeAdditiveSymmetricAction_translate
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    (R.toMassFreeAdditiveSymmetricAction hInvariant n).translate k F =
      R.realizableCarrierTranslation hInvariant n k F :=
  rfl

/-- Pure OS geometry at one realizable lattice step:

`‖T₁F‖² = ⟪F,T₂F⟫`.

No contraction or numerical mass is used. -/
theorem realizableCarrierTranslation_one_norm_sq_eq_inner_two_massFree
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖R.realizableCarrierTranslation hInvariant n 1 F‖ ^ 2 =
      inner ℝ F (R.realizableCarrierTranslation hInvariant n 2 F) := by
  simpa using
    (R.toMassFreeAdditiveSymmetricAction hInvariant n).norm_translate_sq_eq_inner_double
      (1 : ℕ) F

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

/-- Literal compact-Haar shared-boundary Dirichlet energy of one vacuum-centered
actual finite Wilson carrier.

It is the boundary Gram-moment norm-square loss over one genuine integer
lattice-time step. The declaration is explicitly mass-free and does not reuse
the legacy exact-value declaration name. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
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
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) : ℝ :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  (∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) -
    ∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 Fc) b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

/-- The geometric two-step OS defect is exactly the literal compact-Haar
boundary Dirichlet energy, with no exact-value module in the proof route. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy_massFree
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
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    inner ℝ Fc Fc -
        inner ℝ Fc (R.realizableCarrierTranslation hInvariant n 2 Fc) =
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  let F1 := R.realizableCarrierTranslation hInvariant n 1 Fc
  have hdouble :=
    R.realizableCarrierTranslation_one_norm_sq_eq_inner_two_massFree
      hInvariant n Fc
  have hnorm0 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc
  have hnorm1 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
  change
    inner ℝ Fc Fc - inner ℝ Fc
        (R.realizableCarrierTranslation hInvariant n 2 Fc) = _
  rw [real_inner_self_eq_norm_sq, ← hdouble]
  change ‖Fc‖ ^ 2 - ‖F1‖ ^ 2 = _
  rw [hnorm0, hnorm1]
  rfl

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

/-- The intrinsic centered one-step operator norm from #1511 theorem-generates
the exact Poincaré inequality for the geometric two-step OS defect.

The coefficient is not prescribed: it is definitionally
`1 - ‖T₁|centered‖²`. -/
theorem centered_geometricDirichlet_coercivity
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    (1 - (A.centeredTransferFactor n) ^ 2) * ‖Fc‖ ^ 2 ≤
      inner ℝ Fc Fc -
        inner ℝ Fc (R.realizableCarrierTranslation hInvariant n 2 Fc) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  have hnorm :
      ‖R.realizableCarrierTranslation hInvariant n 1 Fc‖ ≤
        A.centeredTransferFactor n * ‖Fc‖ := by
    simpa only [Pn, Fc] using
      A.toCenteredOperatorNormRealizableOneStepGapCertificate.oneStep_centered_norm_le n F
  exact
    ((R.toMassFreeAdditiveSymmetricAction hInvariant n).norm_translate_le_iff_dirichlet_defect
      (1 : ℕ) (A.centeredTransferFactor n) (A.centeredTransferFactor_nonneg n) Fc).1
      (by simpa only using hnorm)

/-- Therefore #1511's intrinsic excitation-sector rate has a literal
compact-Haar boundary Poincaré form.  The true finite analytic residual is now
the behavior of the actual Wilson boundary Dirichlet energy, not an injected
mass value. -/
theorem centered_boundaryDirichlet_poincare
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    (1 - (A.centeredTransferFactor n) ^ 2) *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Fc := Pn.vacuumCenteredCarrier F
  have hcoercive := A.centered_geometricDirichlet_coercivity n F
  have hnorm0 :=
    physical_yang_mills_evenPeriodicWilsonOS_carrier_norm_sq_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc
  have henergy :=
    physical_yang_mills_evenPeriodicWilsonOS_centered_geometricDirichlet_eq_boundaryDirichletEnergy_massFree
      R hInvariant n F
  calc
    (1 - (A.centeredTransferFactor n) ^ 2) *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) =
      (1 - (A.centeredTransferFactor n) ^ 2) * ‖Fc‖ ^ 2 := by
        rw [hnorm0]
    _ ≤ inner ℝ Fc Fc -
        inner ℝ Fc (R.realizableCarrierTranslation hInvariant n 2 Fc) := hcoercive
    _ = physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F := henergy

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

end MathlibAnalytic
end MGAP4D

end