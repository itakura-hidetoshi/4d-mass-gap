import MGAP4D.Spectral.Basic

namespace MGAP4D
namespace Spectral

/-- A minimal migration-level witness that a positive rational gap value is recorded. -/
structure GapWitness where
  gap : SpectralValue
  positiveNumerator : gap.value.num > 0

def gap3320Witness : GapWitness :=
  { gap := spectral3320,
    positiveNumerator := by decide }

theorem gap3320_value : gap3320Witness.gap.value = 33 / 20 := by
  rfl

end Spectral
end MGAP4D
