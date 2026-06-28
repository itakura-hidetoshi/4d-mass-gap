import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeContractionSemigroup

/-- The canonical completed semigroup evaluates through the previously
constructed physical time-translation operator. -/
@[simp] theorem toPhysicalSemigroup_operator
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) :
    T.toPhysicalSemigroup.operator t = T.physicalOperator t :=
  rfl

/-- Compile-smoke receipt for the complete physical contraction-semigroup laws. -/
theorem toPhysicalSemigroup_laws
    (T : P.PositiveTimeContractionSemigroup) :
    T.toPhysicalSemigroup.operator 0 =
        ContinuousLinearMap.id ℝ P.PhysicalHilbert ∧
      (∀ s t, T.toPhysicalSemigroup.operator (s + t) =
        (T.toPhysicalSemigroup.operator s).comp
          (T.toPhysicalSemigroup.operator t)) ∧
      (∀ t, ‖T.toPhysicalSemigroup.operator t‖ ≤ 1) ∧
      (∀ t, T.toPhysicalSemigroup.operator t P.vacuum = P.vacuum) := by
  exact ⟨
    T.toPhysicalSemigroup.operator_zero,
    T.toPhysicalSemigroup.operator_add,
    T.toPhysicalSemigroup.opNorm_le,
    T.toPhysicalSemigroup.fixes_vacuum⟩

end PositiveTimeContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
