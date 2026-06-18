import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The three possible positions of a non-target boundary link inside a
plaquette incident to a fixed target link. -/
inductive PeriodicHypercubicOtherEdgeKind where
  | parallel
  | startTransverse
  | endTransverse
  deriving DecidableEq, Fintype

/-- Exact finite data indexing the eighteen candidate active neighbors of a
physical link in four dimensions: three transverse axes, two sides, and three
other boundary positions. -/
abbrev PeriodicHypercubicOtherEdgeData
    (mu : PeriodicHypercubicAxis) : Type :=
  PeriodicHypercubicOtherAxis mu ×
    (Bool × PeriodicHypercubicOtherEdgeKind)

/-- There are exactly three non-target boundary positions. -/
theorem periodicHypercubicOtherEdgeKind_card :
    Fintype.card PeriodicHypercubicOtherEdgeKind = 3 := by
  native_decide

/-- The canonical candidate-data type has exactly `3 * 2 * 3 = 18` elements. -/
theorem periodicHypercubicOtherEdgeData_card
    (mu : PeriodicHypercubicAxis) :
    Fintype.card (PeriodicHypercubicOtherEdgeData mu) = 18 := by
  rw [Fintype.card_prod, periodicHypercubicOtherAxis_card,
    Fintype.card_prod, periodicHypercubicOtherEdgeKind_card]
  native_decide

/-- Translation in one direction commutes with inverse translation in another. -/
theorem periodicHypercubicShift_unshift_comm
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n (periodicHypercubicUnshift n x nu) mu =
      periodicHypercubicUnshift n (periodicHypercubicShift n x mu) nu := by
  unfold periodicHypercubicShift periodicHypercubicUnshift
  abel

@[simp] theorem periodicHypercubicPlaquetteFirstAxis_mk
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) (hlt : mu < nu) :
    periodicHypercubicPlaquetteFirstAxis
      (x, ⟨(mu, nu), hlt⟩ : PeriodicHypercubicPlaquette n) = mu :=
  rfl

@[simp] theorem periodicHypercubicPlaquetteSecondAxis_mk
    (n : ℕ) (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) (hlt : mu < nu) :
    periodicHypercubicPlaquetteSecondAxis
      (x, ⟨(mu, nu), hlt⟩ : PeriodicHypercubicPlaquette n) = nu :=
  rfl

/-- The physical link selected by one of the eighteen canonical neighbor
positions around a target link. -/
def periodicHypercubicOtherEdgeCandidate
    (n : ℕ) (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherEdgeData target.2) :
    PeriodicHypercubicEdge n :=
  let nu := data.1.1
  let side := data.2.1
  match data.2.2 with
  | .parallel =>
      (if side then
          periodicHypercubicUnshift n target.1 nu
        else
          periodicHypercubicShift n target.1 nu,
        target.2)
  | .startTransverse =>
      (if side then
          periodicHypercubicUnshift n target.1 nu
        else
          target.1,
        nu)
  | .endTransverse =>
      (if side then
          periodicHypercubicUnshift n
            (periodicHypercubicShift n target.1 target.2) nu
        else
          periodicHypercubicShift n target.1 target.2,
        nu)

/-- Every canonical other-edge candidate is distinct from the target once a
unit lattice translation is nontrivial. -/
theorem periodicHypercubicOtherEdgeCandidate_ne_target
    (n : ℕ) (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherEdgeData target.2) :
    periodicHypercubicOtherEdgeCandidate n target data ≠ target := by
  rcases target with ⟨x, mu⟩
  rcases data with ⟨⟨nu, hne⟩, side, kind⟩
  cases side <;> cases kind
  · intro h
    exact periodicHypercubicShift_ne_self n hn x nu
      (congrArg Prod.fst h)
  · intro h
    exact hne (congrArg Prod.snd h)
  · intro h
    exact hne (congrArg Prod.snd h)
  · intro h
    exact periodicHypercubicUnshift_ne_self n hn x nu
      (congrArg Prod.fst h)
  · intro h
    exact hne (congrArg Prod.snd h)
  · intro h
    exact hne (congrArg Prod.snd h)

/-- Each canonical candidate is a genuine physical boundary link of its
corresponding incident plaquette. -/
theorem periodicHypercubicOtherEdgeCandidate_touches_incident
    (n : ℕ) (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherEdgeData target.2) :
    periodicHypercubicPlaquetteTouchesEdge n
      (periodicHypercubicIncidentPlaquette n target data.1 data.2.1)
      (periodicHypercubicOtherEdgeCandidate n target data) := by
  rcases target with ⟨x, mu⟩
  rcases data with ⟨⟨nu, hne⟩, side, kind⟩
  by_cases hlt : mu < nu
  · cases side <;> cases kind
    · refine ⟨2, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨3, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨1, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨0, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨3, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨1, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt,
        periodicHypercubicShift_unshift_comm]
  · cases side <;> cases kind
    · refine ⟨1, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨0, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨2, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨3, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨0, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨2, ?_⟩
      simp [periodicHypercubicPhysicalBoundaryEdge,
        periodicHypercubicOtherEdgeCandidate,
        periodicHypercubicIncidentPlaquette,
        periodicHypercubicAxisPairOfNe, hlt,
        periodicHypercubicShift_unshift_comm]

/-- Every canonical candidate belongs to the non-target boundary-link set of
its corresponding incident plaquette. -/
theorem periodicHypercubicOtherEdgeCandidate_mem_otherEdges
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherEdgeData target.2) :
    periodicHypercubicOtherEdgeCandidate n target data ∈
      periodicHypercubicPlaquetteOtherEdges n target
        (periodicHypercubicIncidentPlaquette n target data.1 data.2.1) := by
  classical
  unfold periodicHypercubicPlaquetteOtherEdges
  apply Finset.mem_erase.mpr
  constructor
  · exact periodicHypercubicOtherEdgeCandidate_ne_target n hn target data
  · unfold periodicHypercubicPlaquetteEdges
    apply Finset.mem_image.mpr
    rcases periodicHypercubicOtherEdgeCandidate_touches_incident
      n target data with ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ _, hk⟩

/-- Every one of the eighteen canonical candidates is an active neighbor of
the target link. -/
theorem periodicHypercubicOtherEdgeCandidate_mem_activeNeighbors
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherEdgeData target.2) :
    periodicHypercubicOtherEdgeCandidate n target data ∈
      periodicHypercubicActiveNeighbors n target := by
  classical
  unfold periodicHypercubicActiveNeighbors
  apply Finset.mem_biUnion.mpr
  refine ⟨periodicHypercubicIncidentPlaquette n target data.1 data.2.1, ?_, ?_⟩
  · rw [periodicHypercubic_mem_touchingPlaquettes_iff]
    exact periodicHypercubicIncidentPlaquette_touches
      n target data.1 data.2.1
  · exact periodicHypercubicOtherEdgeCandidate_mem_otherEdges
      n hn target data

end

end MathlibAnalytic
end MGAP4D
