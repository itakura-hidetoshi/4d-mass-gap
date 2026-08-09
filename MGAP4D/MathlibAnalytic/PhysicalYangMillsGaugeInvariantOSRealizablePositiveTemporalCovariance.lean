import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCoherentDiscreteTemporalStationarity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBilinearForm

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizablePositiveTemporalCovarianceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizablePositiveTemporalCovarianceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizablePositiveTemporalCovarianceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizablePositiveTemporalCovarianceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizablePositiveTemporalCovarianceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizablePositiveTemporalCovarianceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Minimal OS compatibility at the physically realizable positive lattice
Euclidean times.

Full-state stationarity and the actual lattice-time realization are supplied by
`R₀`.  The only additional model-side requirements are:

* positive-time observables remain in the chosen physical positive-time
  subalgebra under a nonnegative integer temporal displacement;
* the physical configuration reflection realizes `D.reflection` and reverses
  each realizable integer temporal displacement.

No all-time `NNReal` semigroup on a fixed finite periodic lattice is asserted. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
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
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S) where
  toDiscreteTemporalCovariance :
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance
      S D halfExtent N hN beta hbeta Q E
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g X,
    configurationReflection (S.action g X) =
      S.action g (configurationReflection X)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  reflection_translate_neg_realizable :
    ∀ (n : ℕ) (k : ℕ) X,
      configurationReflection
          (E.translate
            (toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k)) X) =
        E.translate
          (-toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k))
          (configurationReflection X)
  positiveTime_preserved :
    ∀ (n : ℕ) (k : ℕ) (F : D.positiveTimeSubalgebra),
      (toDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation
          n (Int.ofNat k)
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈
        D.positiveTimeSubalgebra

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

/-- The actual full observable automorphism at a nonnegative realizable lattice
Euclidean time. -/
noncomputable def fullTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S ≃ₐ[ℝ]
      physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  R.toDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation
    n (Int.ofNat k)

/-- Restrict the actual full observable automorphism to the physical
positive-time subalgebra at the chosen realizable displacement. -/
noncomputable def positiveTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ) :
    D.positiveTimeSubalgebra →ₐ[ℝ] D.positiveTimeSubalgebra :=
  ((R.fullTranslation n k).toAlgHom.comp D.positiveTimeSubalgebra.val).codRestrict
    D.positiveTimeSubalgebra
    (fun F => R.positiveTime_preserved n k F)

/-- The restricted positive-time translation is definitionally the actual full
physical precomposition after coercion. -/
@[simp] theorem positiveTranslation_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ) (F : D.positiveTimeSubalgebra) :
    (R.positiveTranslation n k F :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      R.fullTranslation n k
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :=
  rfl

/-- The full actual approximating state is stationary under every realizable
nonnegative temporal displacement. -/
theorem approximatingState_fullTranslation_invariant
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
        (R.fullTranslation n k O) =
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n O := by
  exact
    R.toDiscreteTemporalCovariance
      |>.approximatingGaugeInvariantWeakStarState_realizableTime_invariant
        n (Int.ofNat k) O

/-- Reflection converts a realizable positive temporal displacement into the
inverse full observable automorphism. -/
theorem reflection_fullTranslation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    D.reflection (R.fullTranslation n k O) =
      (R.fullTranslation n k).symm (D.reflection O) := by
  rw [R.reflection_realization, R.reflection_realization]
  apply Subtype.ext
  ext X
  simp only [fullTranslation,
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation,
    physicalGaugeInvariantObservablePrecompAlgEquiv_apply,
    physicalGaugeInvariantObservablePrecompAlgEquiv_symm_apply]
  let t := R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k)
  change
    (O : BoundedContinuousFunction S.Configuration ℝ)
        (E.translate t (R.configurationReflection X)) =
      (O : BoundedContinuousFunction S.Configuration ℝ)
        (R.configurationReflection ((E.translate t).symm X))
  have hcancelPlusMinus :
      E.translate t (E.translate (-t) X) = X := by
    rw [← E.translate_add_apply]
    have hzero : t + -t = 0 := by ring
    rw [hzero, E.translate_zero_apply]
  have href :=
    R.reflection_translate_neg_realizable n k (E.translate (-t) X)
  change
    R.configurationReflection
        (E.translate t (E.translate (-t) X)) =
      E.translate (-t)
        (R.configurationReflection (E.translate (-t) X)) at href
  rw [hcancelPlusMinus] at href
  have hforward :
      E.translate t (R.configurationReflection X) =
        R.configurationReflection (E.translate (-t) X) := by
    apply (E.translate (-t)).injective
    calc
      E.translate (-t) (E.translate t (R.configurationReflection X)) =
          R.configurationReflection X := by
        rw [← E.translate_add_apply]
        have hzero : -t + t = 0 := by ring
        rw [hzero, E.translate_zero_apply]
      _ = E.translate (-t)
          (R.configurationReflection (E.translate (-t) X)) := href
  rw [hforward, E.translate_symm_apply_eq_neg]

/-- The theorem-generated finite state stationarity and reflection reversal imply
the realized Osterwalder--Schrader exchange identity.  It does not require an
independent exchange assumption. -/
theorem osBilinForm_positiveTranslation_exchange
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (n k : ℕ)
    (F G : D.positiveTimeSubalgebra) :
    D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        (R.positiveTranslation n k F)
        G =
      D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        F
        (R.positiveTranslation n k G) := by
  let omega := physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
  let A := R.fullTranslation n k
  rw [D.osBilinForm_apply, D.osBilinForm_apply]
  rw [R.positiveTranslation_coe, R.positiveTranslation_coe]
  rw [R.reflection_fullTranslation]
  have hstationary :=
    R.approximatingState_fullTranslation_invariant n k
      (A.symm (D.reflection
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)) *
        (G : physicalYangMillsGaugeInvariantObservableSubalgebra S))
  change
    omega
      (A.symm (D.reflection
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)) *
        (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) =
      omega
        (D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
          A (G : physicalYangMillsGaugeInvariantObservableSubalgebra S))
  calc
    omega
        (A.symm (D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)) *
          (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) =
      omega
        (A
          (A.symm (D.reflection
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)) *
            (G : physicalYangMillsGaugeInvariantObservableSubalgebra S))) :=
      hstationary.symm
    _ = omega
        (A (A.symm (D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S))) *
          A (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) := by
      rw [map_mul]
    _ = omega
        (D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
          A (G : physicalYangMillsGaugeInvariantObservableSubalgebra S)) := by
      rw [A.apply_symm_apply]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

end MathlibAnalytic
end MGAP4D

end
