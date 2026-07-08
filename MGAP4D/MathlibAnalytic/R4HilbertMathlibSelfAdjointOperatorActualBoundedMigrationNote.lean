import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataBoundedActualAccessors

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotient

/-!
# Actual R4 operator boundedness migration note

`R4HilbertMathlibSelfAdjointOperatorData` now carries the continuous
full-domain representative and the full-domain proof directly.

Therefore the bounded actual accessor layer no longer requires a central route
supply. The old route-backed and package layers remain useful as construction
bridges, but the canonical bare actual operator data itself is now strong enough
for downstream boundedness accessors.
-/

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
