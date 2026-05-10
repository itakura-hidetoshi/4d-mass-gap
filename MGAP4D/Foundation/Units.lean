namespace MGAP4D
namespace Foundation

/-- Internal normalized units for MGAP4D v1.6 migration. -/
inductive UnitSystem where
  | internalNormalized
  deriving Repr, DecidableEq

/-- The unit system used for the `33/20` gap statement. -/
def mgapUnitSystem : UnitSystem := UnitSystem.internalNormalized

end Foundation
end MGAP4D
