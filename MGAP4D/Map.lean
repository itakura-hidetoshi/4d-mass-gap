/-
MGAP4D Lean reuse map.
This file is intentionally lightweight: it imports the current proof-kernel modules
and exposes machine-readable String metadata for routing/reuse. Archive maps are in /maps.
-/
import MGAP4D.Global.FinalAssembly
import MGAP4D.R1.Basic
import MGAP4D.R2.Basic
import MGAP4D.R3.Basic
import MGAP4D.R4.Basic
import MGAP4D.R5.Basic
import MGAP4D.R6.Basic
import MGAP4D.R7.Basic

namespace MGAP4D
namespace Map

structure ModuleRecord where
  module : String
  path : String
  tags : List String
  declarationCount : Nat
  deriving Repr, Inhabited

def currentModules : List ModuleRecord := [
  { module := "MGAP4D.Global.FinalAssembly", path := "MGAP4D/Global/FinalAssembly.lean", tags := ["R1", "R2", "R3", "R4", "R5", "R6", "R7", "Global"], declarationCount := 5 },
  { module := "MGAP4D.R1.Basic", path := "MGAP4D/R1/Basic.lean", tags := ["R1", "R2", "R7", "Global"], declarationCount := 18 },
  { module := "MGAP4D.R2.Basic", path := "MGAP4D/R2/Basic.lean", tags := ["R1", "R2", "R3", "R4", "R5", "R7", "Global"], declarationCount := 21 },
  { module := "MGAP4D.R3.Basic", path := "MGAP4D/R3/Basic.lean", tags := ["R2", "R3", "R4", "R7", "Global"], declarationCount := 21 },
  { module := "MGAP4D.R4.Basic", path := "MGAP4D/R4/Basic.lean", tags := ["R1", "R2", "R3", "R4"], declarationCount := 35 },
  { module := "MGAP4D.R5.Basic", path := "MGAP4D/R5/Basic.lean", tags := ["R1", "R2", "R4", "R5", "R7"], declarationCount := 27 },
  { module := "MGAP4D.R6.Basic", path := "MGAP4D/R6/Basic.lean", tags := ["R1", "R2", "R3", "R4", "R5", "R6"], declarationCount := 16 },
  { module := "MGAP4D.R7.Basic", path := "MGAP4D/R7/Basic.lean", tags := ["R2", "R4", "R7"], declarationCount := 38 }
]

def routeOrder : List String := ["R1", "R2", "R3", "R4", "R5", "R6", "R7", "Global"]

def archiveMapFiles : List String := [
  "maps/LEAN_FILE_MAP.json",
  "maps/LEAN_DECLARATION_INDEX.json",
  "maps/LEAN_IMPORT_GRAPH.json",
  "maps/MGAP4D_ROUTE_MAP.json",
  "maps/LEAN_REUSE_MAP.md"
]

end Map
end MGAP4D
