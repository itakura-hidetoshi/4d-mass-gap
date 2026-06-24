import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSObservableTimeTranslationCovariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- Precomposition by a self-homeomorphism is an algebra automorphism of real
bounded continuous functions. -/
noncomputable def boundedContinuousPrecompAlgEquiv
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X) :
    BoundedContinuousFunction X ℝ ≃ₐ[ℝ]
      BoundedContinuousFunction X ℝ where
  toFun O := O.compContinuous h.toContinuousMap
  invFun O := O.compContinuous h.symm.toContinuousMap
  left_inv O := by
    ext x
    simp
  right_inv O := by
    ext x
    simp
  map_mul' O Q := by
    ext x
    rfl
  map_add' O Q := by
    ext x
    rfl
  commutes' r := by
    ext x
    rfl

@[simp]
theorem boundedContinuousPrecompAlgEquiv_apply
    {X : Type*} [TopologicalSpace X]
    (h : Homeomorph X X)
    (O : BoundedContinuousFunction X ℝ)
    (x : X) :
    boundedContinuousPrecompAlgEquiv h O x = O (h x) :=
  rfl

/-- A configuration homeomorphism commuting with every supplied gauge action
induces an algebra automorphism of the gauge-invariant observable algebra. -/
noncomputable def physicalGaugeInvariantObservablePrecompAlgEquiv
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (h : Homeomorph S.Configuration S.Configuration)
    (hGauge : ∀ g A, h (S.action g A) = S.action g (h A)) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S ≃ₐ[ℝ]
      physicalYangMillsGaugeInvariantObservableSubalgebra S where
  toFun O :=
    ⟨boundedContinuousPrecompAlgEquiv h O.1, by
      intro g A
      change O.1 (h (S.action g A)) = O.1 (h A)
      rw [hGauge]
      exact O.2 g (h A)⟩
  invFun O :=
    ⟨boundedContinuousPrecompAlgEquiv h.symm O.1, by
      intro g A
      change O.1 (h.symm (S.action g A)) = O.1 (h.symm A)
      have hGaugeSymm :
          h.symm (S.action g A) = S.action g (h.symm A) := by
        apply h.injective
        simp only [Homeomorph.apply_symm_apply]
        rw [hGauge]
        simp
      rw [hGaugeSymm]
      exact O.2 g (h.symm A)⟩
  left_inv O := by
    apply Subtype.ext
    ext A
    simp
  right_inv O := by
    apply Subtype.ext
    ext A
    simp
  map_mul' O Q := by
    apply Subtype.ext
    ext A
    rfl
  map_add' O Q := by
    apply Subtype.ext
    ext A
    rfl
  commutes' r := by
    apply Subtype.ext
    ext A
    rfl

@[simp]
theorem physicalGaugeInvariantObservablePrecompAlgEquiv_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (h : Homeomorph S.Configuration S.Configuration)
    (hGauge : ∀ g A, h (S.action g A) = S.action g (h A))
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (A : S.Configuration) :
    ((physicalGaugeInvariantObservablePrecompAlgEquiv S h hGauge O :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) A =
      (O : BoundedContinuousFunction S.Configuration ℝ) (h A) :=
  rfl

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Configuration-level geometric data sufficient to construct the full
observable time-translation covariance package.

The time translations are homeomorphisms of the physical configuration space,
commute with every gauge action, preserve the continuum probability law, and
restrict to the already constructed positive-time observable semigroup.
Reflection covariance remains stated on observables because the current
`OSReflectionData` stores reflection abstractly rather than as a configuration
homeomorphism. -/
structure ConfigurationTimeTranslationCovariance
    (T : P.PositiveTimeObservableContractionSemigroup) where
  configurationTranslate : NNReal →
    Homeomorph S.Configuration S.Configuration
  gauge_commute : ∀ t g A,
    configurationTranslate t (S.action g A) =
      S.action g (configurationTranslate t A)
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv S
        (configurationTranslate t) (gauge_commute t)
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F :
        physicalYangMillsGaugeInvariantObservableSubalgebra S)
  reflection_translate : ∀ t O,
    D.reflection
        (physicalGaugeInvariantObservablePrecompAlgEquiv S
          (configurationTranslate t) (gauge_commute t) O) =
      (physicalGaugeInvariantObservablePrecompAlgEquiv S
        (configurationTranslate t) (gauge_commute t)).symm
          (D.reflection O)
  continuumMeasure_invariant : ∀ t,
    Measure.map (configurationTranslate t)
        (S.continuumMeasure : Measure S.Configuration) =
      (S.continuumMeasure : Measure S.Configuration)
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S

namespace ConfigurationTimeTranslationCovariance

/-- Configuration-level time-translation geometry generates the full observable
covariance package used by the OS exchange and self-adjointness bridge. -/
theorem toReflectionTimeTranslationCovariance
    {T : P.PositiveTimeObservableContractionSemigroup}
    (C : T.ConfigurationTimeTranslationCovariance) :
    T.ReflectionTimeTranslationCovariance where
  fullTranslate t :=
    physicalGaugeInvariantObservablePrecompAlgEquiv S
      (C.configurationTranslate t) (C.gauge_commute t)
  positive_restriction := C.positive_restriction
  reflection_translate := C.reflection_translate
  state_invariant := by
    intro t O
    rw [C.omega_eq_continuumState]
    simp only [physicalYangMillsContinuumGaugeInvariantWeakStarState_apply,
      physicalYangMillsContinuumGaugeInvariantExpectation_apply]
    change
      (∫ A,
        (O : BoundedContinuousFunction S.Configuration ℝ)
          (C.configurationTranslate t A)
        ∂(S.continuumMeasure : Measure S.Configuration)) =
      ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
        ∂(S.continuumMeasure : Measure S.Configuration)
    calc
      (∫ A,
          (O : BoundedContinuousFunction S.Configuration ℝ)
            (C.configurationTranslate t A)
          ∂(S.continuumMeasure : Measure S.Configuration)) =
        ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
          ∂Measure.map (C.configurationTranslate t)
            (S.continuumMeasure : Measure S.Configuration) := by
          symm
          exact MeasureTheory.integral_map
            (C.configurationTranslate t).continuous.measurable.aemeasurable
            (O : BoundedContinuousFunction S.Configuration ℝ).continuous.aestronglyMeasurable
      _ = ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
          ∂(S.continuumMeasure : Measure S.Configuration) := by
        rw [C.continuumMeasure_invariant]

/-- Configuration-level time-translation covariance and observable-state strong
continuity imply self-adjointness of the graph-closed physical Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    {T : P.PositiveTimeObservableContractionSemigroup}
    (C : T.ConfigurationTimeTranslationCovariance)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian :=
  C.toReflectionTimeTranslationCovariance.closedRightHamiltonian_isSelfAdjoint
    hContinuous

end ConfigurationTimeTranslationCovariance

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
