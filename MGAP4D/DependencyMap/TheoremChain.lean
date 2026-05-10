namespace MGAP4D
namespace DependencyMap

inductive SurfaceLayer where
  | r1
  | r2
  | r3
  | r4
  | r5
  | r6
  | r7
  | global
  deriving Repr, DecidableEq

structure ChainNode where
  order : Nat
  layer : SurfaceLayer
  name : String
  deriving Repr, DecidableEq

def theoremChain : List ChainNode := [
  { order := 1, layer := SurfaceLayer.r1, name := "R1 theorem surface" },
  { order := 2, layer := SurfaceLayer.r2, name := "R2 theorem surface" },
  { order := 3, layer := SurfaceLayer.r4, name := "R4 lower surface" },
  { order := 4, layer := SurfaceLayer.r3, name := "R3 kernel route surface" },
  { order := 5, layer := SurfaceLayer.r5, name := "R5 spectrum surface" },
  { order := 6, layer := SurfaceLayer.r6, name := "R6 interval surface" },
  { order := 7, layer := SurfaceLayer.r7, name := "R7 exact surface" },
  { order := 8, layer := SurfaceLayer.global, name := "Global final surface" }
]

theorem theoremChain_nonempty : theoremChain.length > 0 := by
  decide

end DependencyMap
end MGAP4D
