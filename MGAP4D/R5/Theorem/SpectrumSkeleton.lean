import MGAP4D.R5.Concrete.SpectrumProofObligationMap

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumSkeleton where
  obligationMapReady : Prop
  setTheoremTarget : Prop
  bottomTheoremTarget : Prop
  witnessTheoremTarget : Prop
  comparisonTheoremTarget : Prop
  infimumTheoremTarget : Prop
  mathlibRequestLinked : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def SpectrumSkeleton.ready (S : SpectrumSkeleton) : Prop :=
  S.obligationMapReady ∧ S.setTheoremTarget ∧ S.bottomTheoremTarget ∧
  S.witnessTheoremTarget ∧ S.comparisonTheoremTarget ∧ S.infimumTheoremTarget ∧
  S.mathlibRequestLinked ∧ S.statusCompatibilityHeld ∧ S.publicBoundaryHeld

theorem spectrum_skeleton_pack
    (S : SpectrumSkeleton) :
    S.ready ↔ S.obligationMapReady ∧ S.setTheoremTarget ∧ S.bottomTheoremTarget ∧
      S.witnessTheoremTarget ∧ S.comparisonTheoremTarget ∧ S.infimumTheoremTarget ∧
      S.mathlibRequestLinked ∧ S.statusCompatibilityHeld ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
