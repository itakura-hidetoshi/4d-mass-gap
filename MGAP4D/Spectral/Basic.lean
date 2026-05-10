namespace MGAP4D
namespace Spectral

/-- Lightweight carrier for a normalized spectral value during migration. -/
structure SpectralValue where
  value : Rat
  deriving Repr, DecidableEq

/-- The normalized spectral value `33/20`. -/
def spectral3320 : SpectralValue :=
  { value := 33 / 20 }

end Spectral
end MGAP4D
