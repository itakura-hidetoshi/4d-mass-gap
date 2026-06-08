import MGAP4D.Spectral.Basic

namespace MGAP4D
namespace Spectral

/-- A minimal migration-level witness that a positive rational gap value is recorded. -/
structure GapWitness where
  gap : SpectralValue
  positiveNumerator : gap.value.num > 0

/-- The normalized `33/20` carrier has a positive numerator.

This proof exposes the concrete rational value before invoking computation, so
it does not depend on `decide` unfolding the named carrier `spectral3320`. -/
theorem spectral3320_num_positive : spectral3320.value.num > 0 := by
  change (33 / 20 : Rat).num > 0
  native_decide

def gap3320Witness : GapWitness :=
  { gap := spectral3320,
    positiveNumerator := spectral3320_num_positive }

theorem gap3320_value : gap3320Witness.gap.value = 33 / 20 := by
  rfl

end Spectral
end MGAP4D
