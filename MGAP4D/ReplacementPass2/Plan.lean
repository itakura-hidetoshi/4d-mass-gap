namespace MGAP4D
namespace ReplacementPass2

inductive Pass2Target where
  | operatorBundle
  | r1ClosureBundle
  | r2r4r3RouteBundle
  | r5r6r7RouteBundle
  | globalConcreteBundle
  | finalAssemblyBundle
  deriving Repr, DecidableEq

structure Pass2PlanEntry where
  order : Nat
  target : Pass2Target
  statusPreserved : Bool
  theoremFacingBundle : Bool
  mathlibRequired : Bool
  deriving Repr, DecidableEq

def pass2Plan : List Pass2PlanEntry := [
  { order := 1, target := Pass2Target.operatorBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false },
  { order := 2, target := Pass2Target.r1ClosureBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false },
  { order := 3, target := Pass2Target.r2r4r3RouteBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false },
  { order := 4, target := Pass2Target.r5r6r7RouteBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false },
  { order := 5, target := Pass2Target.globalConcreteBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false },
  { order := 6, target := Pass2Target.finalAssemblyBundle, statusPreserved := true, theoremFacingBundle := true, mathlibRequired := false }
]

theorem pass2Plan_nonempty : pass2Plan.length > 0 := by
  decide

end ReplacementPass2
end MGAP4D
