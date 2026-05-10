import MGAP4D.Global.FinalAssembly
import MGAP4D.Global.Concrete.Pass2Bundle
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace Global

structure FinalAssemblyPass2Bundle where
  ledgerReady : Prop
  globalSurfaceReady : Prop
  globalConcretePass2Ready : Prop
  finalConcreteReady : Prop
  finalReplacementReady : Prop
  pass2GateReady : Prop
  publicBoundaryHeld : Prop

def FinalAssemblyPass2Bundle.ready (B : FinalAssemblyPass2Bundle) : Prop :=
  B.ledgerReady ∧ B.globalSurfaceReady ∧ B.globalConcretePass2Ready ∧
  B.finalConcreteReady ∧ B.finalReplacementReady ∧ B.pass2GateReady ∧ B.publicBoundaryHeld

theorem final_assembly_pass2_bundle_pack
    (B : FinalAssemblyPass2Bundle) :
    B.ready ↔ B.ledgerReady ∧ B.globalSurfaceReady ∧ B.globalConcretePass2Ready ∧
      B.finalConcreteReady ∧ B.finalReplacementReady ∧ B.pass2GateReady ∧ B.publicBoundaryHeld := by
  rfl

end Global
end MGAP4D
