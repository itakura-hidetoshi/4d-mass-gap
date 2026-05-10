namespace MGAP4D
namespace ProofHardening

inductive HardeningLayer where
  | operatorAPI
  | r1
  | r2
  | r3
  | r4
  | r5
  | r6
  | r7
  | global
  deriving Repr, DecidableEq

inductive HardeningStage where
  | statusInterface
  | theoremSurface
  | dependencyClosed
  | replayChecked
  deriving Repr, DecidableEq

structure HardeningPlanEntry where
  layer : HardeningLayer
  currentStage : HardeningStage
  nextStage : HardeningStage
  ciRequired : Bool
  deriving Repr, DecidableEq

def phase3Plan : List HardeningPlanEntry := [
  { layer := HardeningLayer.operatorAPI, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r1, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r2, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r3, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r4, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r5, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r6, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.r7, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true },
  { layer := HardeningLayer.global, currentStage := HardeningStage.statusInterface, nextStage := HardeningStage.theoremSurface, ciRequired := true }
]

theorem phase3Plan_nonempty : phase3Plan.length > 0 := by
  decide

end ProofHardening
end MGAP4D
