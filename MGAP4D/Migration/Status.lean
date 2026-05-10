namespace MGAP4D
namespace Migration

inductive MigrationStage where
  | scaffold
  | statusInterface
  | theoremSurface
  | replayChecked
  deriving Repr, DecidableEq

structure LayerMigrationStatus where
  layer : String
  stage : MigrationStage
  deferredImports : Bool
  ciRequired : Bool
  deriving Repr, DecidableEq

def currentLayerStatus : List LayerMigrationStatus := [
  { layer := "OperatorAPI", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R1.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R2.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R3.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R4.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R5.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R6.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "R7.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true },
  { layer := "Global.Concrete", stage := MigrationStage.statusInterface, deferredImports := true, ciRequired := true }
]

theorem currentLayerStatus_nonempty : currentLayerStatus.length > 0 := by
  decide

end Migration
end MGAP4D
