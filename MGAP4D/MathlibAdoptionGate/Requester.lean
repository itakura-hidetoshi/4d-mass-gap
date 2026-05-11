import MGAP4D.MathlibAdoptionGate.Policy

namespace MGAP4D
namespace MathlibAdoptionGate

inductive MathlibRequester where
  | r1Hilbert
  | r2Restriction
  | r3ZeroKernel
  | r4LowerBound
  | r5Spectrum
  | r6Interval
  | r7AtomExact
  deriving Repr, DecidableEq

structure MathlibRequest where
  requester : MathlibRequester
  requestedImportGroup : String
  reason : String
  scoped : Bool
  deriving Repr, DecidableEq

def firstEligibleRequesters : List MathlibRequester := [
  MathlibRequester.r1Hilbert,
  MathlibRequester.r2Restriction,
  MathlibRequester.r3ZeroKernel,
  MathlibRequester.r4LowerBound,
  MathlibRequester.r5Spectrum,
  MathlibRequester.r6Interval,
  MathlibRequester.r7AtomExact
]

theorem firstEligibleRequesters_nonempty : firstEligibleRequesters.length > 0 := by
  decide

end MathlibAdoptionGate
end MGAP4D
