import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteTranslationAdjacency
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Membership of one coordinate axis in an ordered periodic plaquette plane. -/
def periodicHypercubicAxisPairContains
    (pair : PeriodicHypercubicAxisPair)
    (mu : PeriodicHypercubicAxis) : Prop :=
  mu = pair.1.1 ∨ mu = pair.1.2

/-- Two periodic plaquette planes share at least one coordinate axis. -/
def periodicHypercubicAxisPairsShareAxis
    (a b : PeriodicHypercubicAxisPair) : Prop :=
  ∃ mu : PeriodicHypercubicAxis,
    periodicHypercubicAxisPairContains a mu ∧
      periodicHypercubicAxisPairContains b mu

/-- The finite graph of the six coordinate planes in four dimensions. Distinct
planes are adjacent exactly when they share one coordinate axis. -/
def periodicHypercubicAxisPairGraph :
    SimpleGraph PeriodicHypercubicAxisPair :=
  { Adj := fun a b => a ≠ b ∧ periodicHypercubicAxisPairsShareAxis a b
    symm := by
      intro a b h
      rcases h with ⟨hne, mu, ha, hb⟩
      exact ⟨Ne.symm hne, mu, hb, ha⟩
    loopless := { irrefl := fun a h => h.1 rfl } }

private def periodicHypercubicAxisPair01 : PeriodicHypercubicAxisPair :=
  ⟨(0, 1), by decide⟩

private def periodicHypercubicAxisPair02 : PeriodicHypercubicAxisPair :=
  ⟨(0, 2), by decide⟩

private def periodicHypercubicAxisPair03 : PeriodicHypercubicAxisPair :=
  ⟨(0, 3), by decide⟩

private def periodicHypercubicAxisPair12 : PeriodicHypercubicAxisPair :=
  ⟨(1, 2), by decide⟩

private def periodicHypercubicAxisPair13 : PeriodicHypercubicAxisPair :=
  ⟨(1, 3), by decide⟩

private def periodicHypercubicAxisPair23 : PeriodicHypercubicAxisPair :=
  ⟨(2, 3), by decide⟩

private theorem periodicHypercubicAxisPair_cases
    (a : PeriodicHypercubicAxisPair) :
    a = periodicHypercubicAxisPair01 ∨
      a = periodicHypercubicAxisPair02 ∨
      a = periodicHypercubicAxisPair03 ∨
      a = periodicHypercubicAxisPair12 ∨
      a = periodicHypercubicAxisPair13 ∨
      a = periodicHypercubicAxisPair23 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_adj_01_02 :
    periodicHypercubicAxisPairGraph.Adj
      periodicHypercubicAxisPair01 periodicHypercubicAxisPair02 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_adj_01_03 :
    periodicHypercubicAxisPairGraph.Adj
      periodicHypercubicAxisPair01 periodicHypercubicAxisPair03 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_adj_01_12 :
    periodicHypercubicAxisPairGraph.Adj
      periodicHypercubicAxisPair01 periodicHypercubicAxisPair12 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_adj_01_13 :
    periodicHypercubicAxisPairGraph.Adj
      periodicHypercubicAxisPair01 periodicHypercubicAxisPair13 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_adj_02_23 :
    periodicHypercubicAxisPairGraph.Adj
      periodicHypercubicAxisPair02 periodicHypercubicAxisPair23 := by
  native_decide

private theorem periodicHypercubicAxisPairGraph_reachable_from_01
    (a : PeriodicHypercubicAxisPair) :
    periodicHypercubicAxisPairGraph.Reachable
      periodicHypercubicAxisPair01 a := by
  rcases periodicHypercubicAxisPair_cases a with
      h | h | h | h | h | h
  · subst a
    exact ⟨SimpleGraph.Walk.nil⟩
  · subst a
    exact ⟨periodicHypercubicAxisPairGraph_adj_01_02.toWalk⟩
  · subst a
    exact ⟨periodicHypercubicAxisPairGraph_adj_01_03.toWalk⟩
  · subst a
    exact ⟨periodicHypercubicAxisPairGraph_adj_01_12.toWalk⟩
  · subst a
    exact ⟨periodicHypercubicAxisPairGraph_adj_01_13.toWalk⟩
  · subst a
    exact ⟨SimpleGraph.Walk.cons
      periodicHypercubicAxisPairGraph_adj_01_02
      periodicHypercubicAxisPairGraph_adj_02_23.toWalk⟩

/-- The six-plane coordinate graph is connected. -/
theorem periodicHypercubicAxisPairGraph_connected :
    periodicHypercubicAxisPairGraph.Connected := by
  intro a b
  rcases periodicHypercubicAxisPairGraph_reachable_from_01 a with ⟨wa⟩
  rcases periodicHypercubicAxisPairGraph_reachable_from_01 b with ⟨wb⟩
  exact ⟨wa.reverse.append wb⟩

/-- If an axis belongs to a plaquette plane, the plaquette touches the positive
physical link based at its base vertex in that axis. -/
theorem periodicHypercubicPlaquetteTouchesBaseAxis
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (pair : PeriodicHypercubicAxisPair)
    (mu : PeriodicHypercubicAxis)
    (hmu : periodicHypercubicAxisPairContains pair mu) :
    periodicHypercubicPlaquetteTouchesEdge n (x, pair) (x, mu) := by
  rcases hmu with hfirst | hsecond
  · subst mu
    exact ⟨0, rfl⟩
  · subst mu
    exact ⟨3, rfl⟩

/-- At one fixed periodic base vertex, changing between distinct plaquette
planes that share an axis gives shared-link plaquette adjacency. -/
theorem periodicHypercubicPlaquetteAdjacent_same_base_of_share_axis
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (a b : PeriodicHypercubicAxisPair)
    (hne : a ≠ b)
    (hshare : periodicHypercubicAxisPairsShareAxis a b) :
    periodicHypercubicPlaquetteAdjacent n (x, a) (x, b) := by
  rcases hshare with ⟨mu, ha, hb⟩
  have hpq : (x, a) ≠ (x, b) := by
    intro h
    exact hne (congrArg Prod.snd h)
  exact periodicHypercubicPlaquetteAdjacent_of_shared_edge n hpq (x, mu)
    (periodicHypercubicPlaquetteTouchesBaseAxis n x a mu ha)
    (periodicHypercubicPlaquetteTouchesBaseAxis n x b mu hb)

/-- The fixed-base inclusion of coordinate planes into periodic plaquettes is a
graph homomorphism. -/
def periodicHypercubicAxisPairToPlaquetteHom
    (n : Nat)
    (x : PeriodicHypercubicVertex n) :
    periodicHypercubicAxisPairGraph →g periodicHypercubicPlaquetteGraph n where
  toFun pair := (x, pair)
  map_rel' := by
    intro a b h
    exact periodicHypercubicPlaquetteAdjacent_same_base_of_share_axis
      n x a b h.1 h.2

/-- Any two periodic plaquettes with the same base vertex are connected through
the finite coordinate-plane orientation graph. -/
theorem periodicHypercubicPlaquetteGraph_reachable_same_base
    (n : Nat)
    (x : PeriodicHypercubicVertex n)
    (a b : PeriodicHypercubicAxisPair) :
    (periodicHypercubicPlaquetteGraph n).Reachable (x, a) (x, b) := by
  rcases periodicHypercubicAxisPairGraph_connected a b with ⟨w⟩
  exact ⟨w.map (periodicHypercubicAxisPairToPlaquetteHom n x)⟩

end

end MathlibAnalytic
end MGAP4D
