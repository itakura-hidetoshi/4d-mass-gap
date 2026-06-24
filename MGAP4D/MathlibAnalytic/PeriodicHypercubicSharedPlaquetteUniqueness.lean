import MGAP4D.MathlibAnalytic.PeriodicHypercubicOtherEdgeUniqueness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The vertex of the unique parallel non-target link on one side of a
canonical target-incident plaquette. -/
def periodicHypercubicIncidentParallelVertex
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool) : PeriodicHypercubicVertex n :=
  if otherSide then
    periodicHypercubicUnshift n target.1 nu.1
  else
    periodicHypercubicShift n target.1 nu.1

@[simp] theorem periodicHypercubicIncidentParallelVertex_false
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentParallelVertex n target nu false =
      periodicHypercubicShift n target.1 nu.1 :=
  rfl

@[simp] theorem periodicHypercubicIncidentParallelVertex_true
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentParallelVertex n target nu true =
      periodicHypercubicUnshift n target.1 nu.1 :=
  rfl

/-- In the nondegenerate periodic regime, a parallel non-target boundary link
recovers both its transverse axis and its side. -/
theorem periodicHypercubicIncidentParallelVertex_injective
    (n : ℕ) (hn : 3 ≤ n)
    (target : PeriodicHypercubicEdge n) :
    Function.Injective
      (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
        periodicHypercubicIncidentParallelVertex n target
          data.1 data.2) := by
  rcases target with ⟨x, mu⟩
  intro a b h
  rcases a with ⟨⟨nuA, hnuA⟩, sideA⟩
  rcases b with ⟨⟨nuB, hnuB⟩, sideB⟩
  cases sideA
  · cases sideB
    · have hAxis := periodicHypercubicShift_axis_injective n
        (by omega) x (by
          simpa [periodicHypercubicIncidentParallelVertex] using h)
      exact Prod.ext (Subtype.ext hAxis) rfl
    · exfalso
      exact periodicHypercubicShift_ne_unshift n hn x nuA nuB (by
        simpa [periodicHypercubicIncidentParallelVertex] using h)
  · cases sideB
    · exfalso
      exact periodicHypercubicShift_ne_unshift n hn x nuB nuA (by
        simpa [periodicHypercubicIncidentParallelVertex] using h.symm)
    · have hAxis := periodicHypercubicUnshift_axis_injective n
        (by omega) x (by
          simpa [periodicHypercubicIncidentParallelVertex] using h)
      exact Prod.ext (Subtype.ext hAxis) rfl

/-- Slot zero is the first transverse non-target link. -/
@[simp] theorem periodicHypercubicIncidentOtherEdge_zero_eq_transverse
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool) :
    periodicHypercubicIncidentOtherEdge n target nu otherSide 0 =
      (periodicHypercubicIncidentTransverseVertex n target nu otherSide 0,
        nu.1) := by
  cases otherSide <;> rfl

/-- Slot one is the second transverse non-target link. -/
@[simp] theorem periodicHypercubicIncidentOtherEdge_one_eq_transverse
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool) :
    periodicHypercubicIncidentOtherEdge n target nu otherSide 1 =
      (periodicHypercubicIncidentTransverseVertex n target nu otherSide 1,
        nu.1) := by
  cases otherSide <;> rfl

/-- Slot two is the parallel non-target link. -/
@[simp] theorem periodicHypercubicIncidentOtherEdge_two_eq_parallel
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool) :
    periodicHypercubicIncidentOtherEdge n target nu otherSide 2 =
      (periodicHypercubicIncidentParallelVertex n target nu otherSide,
        target.2) := by
  cases otherSide <;> rfl

/-- Equality of two transverse non-target links forces equality of the
corresponding canonical incident plaquettes. -/
theorem periodicHypercubicIncidentPlaquette_eq_of_transverse_edge_eq
    (n : ℕ) (hn : 3 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (nuA nuB : PeriodicHypercubicOtherAxis target.2)
    (sideA sideB : Bool)
    (slotA slotB : Fin 2)
    (hEdge :
      (periodicHypercubicIncidentTransverseVertex n target nuA sideA slotA,
          nuA.1) =
        (periodicHypercubicIncidentTransverseVertex n target nuB sideB slotB,
          nuB.1)) :
    periodicHypercubicIncidentPlaquette n target nuA sideA =
      periodicHypercubicIncidentPlaquette n target nuB sideB := by
  have hAxis : nuA.1 = nuB.1 := congrArg Prod.snd hEdge
  have hNu : nuA = nuB := Subtype.ext hAxis
  subst nuB
  have hVertex :
      periodicHypercubicIncidentTransverseVertex n target nuA sideA slotA =
        periodicHypercubicIncidentTransverseVertex n target nuA sideB slotB :=
    congrArg Prod.fst hEdge
  have hData : (sideA, slotA) = (sideB, slotB) :=
    periodicHypercubicIncidentTransverseVertex_injective n hn target nuA hVertex
  have hSide : sideA = sideB := congrArg Prod.fst hData
  subst sideB
  rfl

/-- Equality of two parallel non-target links forces equality of the
corresponding canonical incident plaquettes. -/
theorem periodicHypercubicIncidentPlaquette_eq_of_parallel_vertex_eq
    (n : ℕ) (hn : 3 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (nuA nuB : PeriodicHypercubicOtherAxis target.2)
    (sideA sideB : Bool)
    (hVertex :
      periodicHypercubicIncidentParallelVertex n target nuA sideA =
        periodicHypercubicIncidentParallelVertex n target nuB sideB) :
    periodicHypercubicIncidentPlaquette n target nuA sideA =
      periodicHypercubicIncidentPlaquette n target nuB sideB := by
  have hData : (nuA, sideA) = (nuB, sideB) :=
    periodicHypercubicIncidentParallelVertex_injective n hn target hVertex
  cases hData
  rfl

/-- In a periodic box of side at least three, equality of two enumerated
non-target links forces equality of their canonical target-incident
plaquettes. -/
theorem periodicHypercubicIncidentPlaquette_eq_of_other_edge_eq
    (n : ℕ) (hn : 3 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (nuA nuB : PeriodicHypercubicOtherAxis target.2)
    (sideA sideB : Bool)
    (slotA slotB : Fin 3)
    (hEdge :
      periodicHypercubicIncidentOtherEdge n target nuA sideA slotA =
        periodicHypercubicIncidentOtherEdge n target nuB sideB slotB) :
    periodicHypercubicIncidentPlaquette n target nuA sideA =
      periodicHypercubicIncidentPlaquette n target nuB sideB := by
  fin_cases slotA
  · fin_cases slotB
    · exact periodicHypercubicIncidentPlaquette_eq_of_transverse_edge_eq
        n hn target nuA nuB sideA sideB 0 0 (by simpa using hEdge)
    · exact periodicHypercubicIncidentPlaquette_eq_of_transverse_edge_eq
        n hn target nuA nuB sideA sideB 0 1 (by simpa using hEdge)
    · exfalso
      apply nuA.2
      simpa using congrArg Prod.snd hEdge
  · fin_cases slotB
    · exact periodicHypercubicIncidentPlaquette_eq_of_transverse_edge_eq
        n hn target nuA nuB sideA sideB 1 0 (by simpa using hEdge)
    · exact periodicHypercubicIncidentPlaquette_eq_of_transverse_edge_eq
        n hn target nuA nuB sideA sideB 1 1 (by simpa using hEdge)
    · exfalso
      apply nuA.2
      simpa using congrArg Prod.snd hEdge
  · fin_cases slotB
    · exfalso
      apply nuB.2
      simpa using (congrArg Prod.snd hEdge).symm
    · exfalso
      apply nuB.2
      simpa using (congrArg Prod.snd hEdge).symm
    · apply periodicHypercubicIncidentPlaquette_eq_of_parallel_vertex_eq
        n hn target nuA nuB sideA sideB
      simpa using congrArg Prod.fst hEdge

/-- The actual coordinate plaquettes touching both physical links. -/
noncomputable def periodicHypercubicSharedPlaquettes
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n) :
    Finset (PeriodicHypercubicPlaquette n) := by
  classical
  exact (periodicHypercubicTouchingPlaquettes n target).filter fun p =>
    periodicHypercubicPlaquetteTouchesEdge n p source

@[simp] theorem periodicHypercubic_mem_sharedPlaquettes_iff
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n)
    (p : PeriodicHypercubicPlaquette n) :
    p ∈ periodicHypercubicSharedPlaquettes n target source ↔
      periodicHypercubicPlaquetteTouchesEdge n p target ∧
      periodicHypercubicPlaquetteTouchesEdge n p source := by
  classical
  simp [periodicHypercubicSharedPlaquettes,
    periodicHypercubic_mem_touchingPlaquettes_iff]

/-- Two distinct physical links determine at most one common coordinate
plaquette in the nondegenerate periodic regime. -/
theorem periodicHypercubicPlaquette_eq_of_touches_two_edges
    (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (target source : PeriodicHypercubicEdge n)
    (hNe : source ≠ target)
    (p q : PeriodicHypercubicPlaquette n)
    (hpTarget : periodicHypercubicPlaquetteTouchesEdge n p target)
    (hpSource : periodicHypercubicPlaquetteTouchesEdge n p source)
    (hqTarget : periodicHypercubicPlaquetteTouchesEdge n q target)
    (hqSource : periodicHypercubicPlaquetteTouchesEdge n q source) :
    p = q := by
  have hpMem :=
    periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches
      n p target hpTarget
  have hqMem :=
    periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches
      n q target hqTarget
  unfold periodicHypercubicIncidentPlaquettes at hpMem hqMem
  rcases Finset.mem_image.mp hpMem with ⟨⟨nuP, sideP⟩, _hpData, rfl⟩
  rcases Finset.mem_image.mp hqMem with ⟨⟨nuQ, sideQ⟩, _hqData, rfl⟩
  rcases periodicHypercubicIncidentPlaquette_other_edge_classification
      n target source nuP sideP hpSource hNe with ⟨slotP, hslotP⟩
  rcases periodicHypercubicIncidentPlaquette_other_edge_classification
      n target source nuQ sideQ hqSource hNe with ⟨slotQ, hslotQ⟩
  exact periodicHypercubicIncidentPlaquette_eq_of_other_edge_eq
    n hn target nuP nuQ sideP sideQ slotP slotQ
      (hslotP.trans hslotQ.symm)

/-- For distinct physical links and side length at least three, the concrete
shared-plaquette multiplicity is at most one. -/
theorem periodicHypercubicSharedPlaquettes_card_le_one
    (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (target source : PeriodicHypercubicEdge n)
    (hNe : source ≠ target) :
    (periodicHypercubicSharedPlaquettes n target source).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rw [periodicHypercubic_mem_sharedPlaquettes_iff] at hp hq
  exact periodicHypercubicPlaquette_eq_of_touches_two_edges
    n hn target source hNe p q hp.1 hp.2 hq.1 hq.2

end

end MathlibAnalytic
end MGAP4D
