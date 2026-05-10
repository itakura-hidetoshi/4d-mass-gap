import MGAP4D.OSPositivity.Basic

namespace MGAP4D
namespace OSPositivity

/-- Minimal carrier for reflection data used by the OS reconstruction path. -/
structure ReflectionRecord where
  check : OSPositivityCheck
  reflectionLabel : String
  deriving Repr, DecidableEq

/-- Migration-level reflection record attached to the baseline OS check. -/
def baselineReflectionRecord : ReflectionRecord :=
  { check := basicOSCheck, reflectionLabel := "time reflection" }

theorem baselineReflection_passed : baselineReflectionRecord.check.passed = true := by
  rfl

end OSPositivity
end MGAP4D
