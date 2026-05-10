namespace MGAP4D
namespace Archive

inductive PriorKernelClass where
  | pending
  | reviewed
  | superseded
  deriving Repr, DecidableEq

structure PriorKernelGroup where
  name : String
  klass : PriorKernelClass
  activeImportAllowed : Bool
  reviewRequired : Bool
  deriving Repr, DecidableEq

def priorKernelGroups : List PriorKernelGroup := [
  { name := "v1_0_final prior Lean project archive", klass := PriorKernelClass.pending, activeImportAllowed := false, reviewRequired := true },
  { name := "v0_9 manifest family", klass := PriorKernelClass.pending, activeImportAllowed := false, reviewRequired := true },
  { name := "earlier R1-R7 scaffold variants", klass := PriorKernelClass.pending, activeImportAllowed := false, reviewRequired := true },
  { name := "earlier Global final assembly variants", klass := PriorKernelClass.pending, activeImportAllowed := false, reviewRequired := true },
  { name := "map and declaration index material", klass := PriorKernelClass.pending, activeImportAllowed := false, reviewRequired := true }
]

theorem priorKernelGroups_nonempty : priorKernelGroups.length > 0 := by
  decide

end Archive
end MGAP4D
