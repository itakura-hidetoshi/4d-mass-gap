namespace MGAP4D
namespace Plaquette

/-- Minimal carrier for a plaquette label in the migration spine. -/
structure PlaquetteLabel where
  name : String
  deriving Repr, DecidableEq

/-- The canonical plaquette label used by the witness notation. -/
def p : PlaquetteLabel :=
  { name := "p" }

end Plaquette
end MGAP4D
