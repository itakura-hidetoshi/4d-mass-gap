import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Sufficient full-observable covariance data for the Osterwalder--Schrader
reflection/time-translation exchange identity.

For each nonnegative Euclidean time, `fullTranslate` is an algebra automorphism
of the full physical gauge-invariant observable algebra.  Its restriction to the
positive-time algebra is the supplied contraction-semigroup translation.
Reflection converts forward translation into the inverse automorphism, and the
physical weak-star state is invariant under the forward automorphism. -/
structure ReflectionTimeTranslationCovariance
    (T : P.PositiveTimeObservableContractionSemigroup) where
  fullTranslate : NNReal →
    physicalYangMillsGaugeInvariantObservableSubalgebra S ≃ₐ[ℝ]
      physicalYangMillsGaugeInvariantObservableSubalgebra S
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    fullTranslate t
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F : physicalYangMillsGaugeInvariantObservableSubalgebra S)
  reflection_translate : ∀ t O,
    D.reflection (fullTranslate t O) =
      (fullTranslate t).symm (D.reflection O)
  state_invariant : ∀ t O,
    P.omega (fullTranslate t O) = P.omega O

namespace ReflectionTimeTranslationCovariance

/-- Full observable time-translation covariance implies the exact exchange of
positive-time translation between the two entries of the OS form. -/
theorem toReflectionTimeTranslationExchange
    {T : P.PositiveTimeObservableContractionSemigroup}
    (C : T.ReflectionTimeTranslationCovariance) :
    T.ReflectionTimeTranslationExchange := by
  intro t F G
  rw [D.osBilinForm_apply, D.osBilinForm_apply]
  change
    P.omega
        (D.reflection
            ((T.translate t (P.positiveTimeElement F) :
                D.positiveTimeSubalgebra) :
              physicalYangMillsGaugeInvariantObservableSubalgebra S) *
          G.toGaugeInvariant) =
      P.omega
        (D.reflection F.toGaugeInvariant *
          ((T.translate t (P.positiveTimeElement G) :
              D.positiveTimeSubalgebra) :
            physicalYangMillsGaugeInvariantObservableSubalgebra S))
  rw [← C.positive_restriction t (P.positiveTimeElement F),
    ← C.positive_restriction t (P.positiveTimeElement G),
    C.reflection_translate]
  let alpha := C.fullTranslate t
  change
    P.omega (alpha.symm (D.reflection F.toGaugeInvariant) * G.toGaugeInvariant) =
      P.omega (D.reflection F.toGaugeInvariant * alpha G.toGaugeInvariant)
  calc
    P.omega
        (alpha.symm (D.reflection F.toGaugeInvariant) * G.toGaugeInvariant) =
      P.omega
        (alpha
          (alpha.symm (D.reflection F.toGaugeInvariant) * G.toGaugeInvariant)) := by
        symm
        exact C.state_invariant t _
    _ = P.omega
        (D.reflection F.toGaugeInvariant * alpha G.toGaugeInvariant) := by
      apply congrArg P.omega
      rw [map_mul, alpha.apply_symm_apply]

/-- Full observable covariance and observable-state strong continuity imply
self-adjointness of the graph-closed physical right Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    {T : P.PositiveTimeObservableContractionSemigroup}
    (C : T.ReflectionTimeTranslationCovariance)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian :=
  T.closedRightHamiltonian_isSelfAdjoint_of_reflectionTimeTranslationExchange
    C.toReflectionTimeTranslationExchange hContinuous

end ReflectionTimeTranslationCovariance

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
