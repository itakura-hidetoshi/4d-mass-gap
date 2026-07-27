import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Rebase one OS carrier onto another reflected state while preserving the
underlying positive-time observable exactly.

The two carriers may carry different OS seminorms, null spaces, separation
quotients, and Hilbert completions.  Their raw carrier types nevertheless encode
precisely the same positive-time observable algebra, so the observable itself
provides a canonical real-linear equivalence. -/
noncomputable def carrierRebase
    (P Q : D.OSPreHilbertData) :
    P.Carrier ≃ₗ[ℝ] Q.Carrier where
  toFun := fun F =>
    Q.carrierOfPositiveTime (P.positiveTimeElement F)
  invFun := fun G =>
    P.carrierOfPositiveTime (Q.positiveTimeElement G)
  left_inv := by
    intro F
    rw [Q.positiveTimeElement_carrierOfPositiveTime,
      P.carrierOfPositiveTime_positiveTimeElement]
  right_inv := by
    intro G
    rw [P.positiveTimeElement_carrierOfPositiveTime,
      Q.carrierOfPositiveTime_positiveTimeElement]
  map_add' := by
    intro F G
    apply Carrier.observable_injective Q
    rfl
  map_smul' := by
    intro r F
    apply Carrier.observable_injective Q
    rfl

@[simp] theorem carrierRebase_apply
    (P Q : D.OSPreHilbertData)
    (F : P.Carrier) :
    P.carrierRebase Q F =
      Q.carrierOfPositiveTime (P.positiveTimeElement F) :=
  rfl

/-- Carrier rebasing leaves the represented positive-time observable unchanged. -/
@[simp] theorem positiveTimeElement_carrierRebase
    (P Q : D.OSPreHilbertData)
    (F : P.Carrier) :
    Q.positiveTimeElement (P.carrierRebase Q F) =
      P.positiveTimeElement F := by
  rw [carrierRebase_apply,
    Q.positiveTimeElement_carrierOfPositiveTime]

/-- Rebasing twice through any intermediate OS state is the direct rebase. -/
theorem carrierRebase_trans
    (P Q R : D.OSPreHilbertData)
    (F : P.Carrier) :
    Q.carrierRebase R (P.carrierRebase Q F) =
      P.carrierRebase R F := by
  apply Carrier.observable_injective R
  rfl

/-- Rebasing from an OS carrier back to itself is the identity. -/
@[simp] theorem carrierRebase_self
    (P : D.OSPreHilbertData)
    (F : P.Carrier) :
    P.carrierRebase P F = F := by
  exact (P.carrierRebase P).left_inv F

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
