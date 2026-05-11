import MGAP4D.R5.Concrete.SpectrumTheoremChecklist

namespace MGAP4D
namespace R5
namespace Concrete

structure SpectrumProofObligationMap where
  setToFutureModule : Prop
  bottomToFutureModule : Prop
  witnessToFutureModule : Prop
  comparisonToFutureModule : Prop
  infimumToFutureModule : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityLinked : Prop
  publicBoundaryLinked : Prop

def SpectrumProofObligationMap.ready (M : SpectrumProofObligationMap) : Prop :=
  M.setToFutureModule ∧ M.bottomToFutureModule ∧ M.witnessToFutureModule ∧
  M.comparisonToFutureModule ∧ M.infimumToFutureModule ∧ M.mathlibRequestLinked ∧
  M.statusCompatibilityLinked ∧ M.publicBoundaryLinked

theorem spectrum_proof_obligation_map_pack
    (M : SpectrumProofObligationMap) :
    M.ready ↔ M.setToFutureModule ∧ M.bottomToFutureModule ∧ M.witnessToFutureModule ∧
      M.comparisonToFutureModule ∧ M.infimumToFutureModule ∧ M.mathlibRequestLinked ∧
      M.statusCompatibilityLinked ∧ M.publicBoundaryLinked := by
  rfl

end Concrete
end R5
end MGAP4D
