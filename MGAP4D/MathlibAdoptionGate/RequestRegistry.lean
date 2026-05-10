import MGAP4D.MathlibAdoptionGate.R1HilbertRequest
import MGAP4D.MathlibAdoptionGate.R2RestrictionRequest
import MGAP4D.MathlibAdoptionGate.R4LowerBoundRequest
import MGAP4D.MathlibAdoptionGate.R5SpectrumRequest
import MGAP4D.MathlibAdoptionGate.R6IntervalRequest
import MGAP4D.MathlibAdoptionGate.R7AtomExactRequest

namespace MGAP4D
namespace MathlibAdoptionGate

structure MathlibRequestRegistry where
  r1HilbertRecorded : Prop
  r2RestrictionRecorded : Prop
  r4LowerBoundRecorded : Prop
  r5SpectrumRecorded : Prop
  r6IntervalRecorded : Prop
  r7AtomExactRecorded : Prop
  allScoped : Prop
  publicBoundaryHeld : Prop

def MathlibRequestRegistry.ready (R : MathlibRequestRegistry) : Prop :=
  R.r1HilbertRecorded ∧ R.r2RestrictionRecorded ∧ R.r4LowerBoundRecorded ∧
  R.r5SpectrumRecorded ∧ R.r6IntervalRecorded ∧ R.r7AtomExactRecorded ∧
  R.allScoped ∧ R.publicBoundaryHeld

theorem mathlib_request_registry_pack
    (R : MathlibRequestRegistry) :
    R.ready ↔ R.r1HilbertRecorded ∧ R.r2RestrictionRecorded ∧ R.r4LowerBoundRecorded ∧
      R.r5SpectrumRecorded ∧ R.r6IntervalRecorded ∧ R.r7AtomExactRecorded ∧
      R.allScoped ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
