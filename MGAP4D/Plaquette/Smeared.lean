import MGAP4D.Plaquette.Basic

namespace MGAP4D
namespace Plaquette

/-- Minimal carrier for a compactly supported smearing label. -/
structure SmearingLabel where
  name : String
  compactSupport : Bool
  deriving Repr, DecidableEq

/-- The canonical smearing label `g` in the migrated witness notation. -/
def g : SmearingLabel :=
  { name := "g", compactSupport := true }

/-- Migration-level smeared centered plaquette observable carrier. -/
structure SmearedPlaquetteObservable where
  plaquette : PlaquetteLabel
  smearing : SmearingLabel
  centered : Bool
  deriving Repr, DecidableEq

/-- The symbolic observable `A_{p,g}` used by the final theorem spine. -/
def A_pg : SmearedPlaquetteObservable :=
  { plaquette := p, smearing := g, centered := true }

theorem A_pg_centered : A_pg.centered = true := by
  rfl

theorem A_pg_compactSupport : A_pg.smearing.compactSupport = true := by
  rfl

end Plaquette
end MGAP4D
