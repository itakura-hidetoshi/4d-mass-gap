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
      refine { symm := ?_ }
      intro a b h
      rcases h with ⟨hne, mu, ha, hb⟩
      exact ⟨Ne.symm hne, mu, hb, ha⟩
    loopless := { irrefl := fun a h => h.1 rfl } }

/-- The six-plane coordinate graph is connected. -/
theorem periodicHypercubicAxisPairGraph_connected :
    periodicHypercubicAxisPairGraph.Connected := by
  native_decide

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
  apply periodicHypercubicPlaquetteAdjacent_of_shared_edge n
  · intro hpq
    exact hne (congrArg Prod.snd hpq)
  · exact (x, mu)
  · exact periodicHypercubicPlaquetteTouchesBaseAxis n x a mu ha
  · exact periodicHypercubicPlaquetteTouchesBaseAxis n x b mu hb

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
at most the finite coordinate-plane orientation graph. -/
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
