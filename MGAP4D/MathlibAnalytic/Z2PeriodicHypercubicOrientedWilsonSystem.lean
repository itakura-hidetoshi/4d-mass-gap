import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSystem
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Convert the signed periodic-hypercubic boundary incidence to the generic
orientation-aware boundary-step type. -/
def periodicHypercubicOrientedBoundaryStep
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    FiniteOrientedBoundaryStep (PeriodicHypercubicEdge n) :=
  let step := periodicHypercubicBoundaryStep n p k
  { edge := step.edge
    orientation :=
      match step.orientation with
      | .forward => .forward
      | .backward => .backward }

@[simp] theorem periodicHypercubicOrientedBoundaryStep_edge
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    (periodicHypercubicOrientedBoundaryStep n p k).edge =
      periodicHypercubicPhysicalBoundaryEdge n p k :=
  rfl

@[simp] theorem periodicHypercubicOrientedBoundaryStep_initial
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    (periodicHypercubicOrientedBoundaryStep n p k).initial
        (periodicHypercubicEdgeSource n)
        (periodicHypercubicEdgeTarget n) =
      (periodicHypercubicBoundaryStep n p k).source := by
  fin_cases k <;> rfl

@[simp] theorem periodicHypercubicOrientedBoundaryStep_terminal
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    (periodicHypercubicOrientedBoundaryStep n p k).terminal
        (periodicHypercubicEdgeSource n)
        (periodicHypercubicEdgeTarget n) =
      (periodicHypercubicBoundaryStep n p k).target := by
  fin_cases k <;> rfl

/-- The orientation-correct finite `Z₂` Wilson system on the periodic
four-dimensional hypercubic lattice.  Configurations assign one `Z₂` value to
each physical positive link; backward plaquette traversal uses its inverse. -/
def z2PeriodicHypercubicOrientedWilsonSystem
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    FiniteOrientedLatticeWilsonSystem :=
  { Gauge := Z2Gauge
    Vertex := PeriodicHypercubicVertex n
    Edge := PeriodicHypercubicEdge n
    Plaquette := PeriodicHypercubicPlaquette n
    edgeSource := periodicHypercubicEdgeSource n
    edgeTarget := periodicHypercubicEdgeTarget n
    boundary := periodicHypercubicOrientedBoundaryStep n
    boundary_cycle_01 := by
      intro p
      simpa using periodicHypercubic_boundary_cycle_01 n p
    boundary_cycle_12 := by
      intro p
      simpa using periodicHypercubic_boundary_cycle_12 n p
    boundary_cycle_23 := by
      intro p
      simpa using periodicHypercubic_boundary_cycle_23 n p
    boundary_cycle_30 := by
      intro p
      simpa using periodicHypercubic_boundary_cycle_30 n p
    plaquetteEnergy := fun g => if g = 1 then 0 else 1
    plaquetteEnergy_nonneg := by
      intro g
      split_ifs <;> norm_num
    plaquetteEnergy_conjInvariant := by
      intro h g
      have hconj : h * g * h⁻¹ = g := by
        rw [mul_comm h g, mul_assoc, mul_inv_cancel, mul_one]
      rw [hconj]
    beta := beta
    beta_nonneg := hBeta }

/-- Membership in the explicit four-link physical boundary is equivalent to
the concrete touching predicate. -/
theorem periodicHypercubic_mem_plaquetteEdges_iff
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) :
    e ∈ periodicHypercubicPlaquetteEdges n p ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  classical
  constructor
  · intro h
    unfold periodicHypercubicPlaquetteEdges at h
    rcases Finset.mem_image.mp h with ⟨k, _hk, rfl⟩
    exact ⟨k, rfl⟩
  · exact periodicHypercubic_mem_plaquetteEdges_of_touches n p e

/-- Concrete membership characterization of the previously defined physical
active-neighbor finset. -/
theorem periodicHypercubic_mem_activeNeighbors_iff
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n) :
    source ∈ periodicHypercubicActiveNeighbors n target ↔
      (∃ p : PeriodicHypercubicPlaquette n,
        periodicHypercubicPlaquetteTouchesEdge n p target ∧
          periodicHypercubicPlaquetteTouchesEdge n p source) ∧
        source ≠ target := by
  classical
  constructor
  · intro h
    unfold periodicHypercubicActiveNeighbors at h
    rcases Finset.mem_biUnion.mp h with ⟨p, hp, hsource⟩
    have hErase := Finset.mem_erase.mp hsource
    refine ⟨⟨p,
      (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mp hp,
      (periodicHypercubic_mem_plaquetteEdges_iff n p source).mp hErase.2⟩,
      hErase.1⟩
  · rintro ⟨⟨p, hpTarget, hpSource⟩, hNe⟩
    unfold periodicHypercubicActiveNeighbors
    apply Finset.mem_biUnion.mpr
    refine ⟨p,
      (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mpr hpTarget,
      ?_⟩
    apply Finset.mem_erase.mpr
    exact ⟨hNe,
      (periodicHypercubic_mem_plaquetteEdges_iff n p source).mpr hpSource⟩

/-- Generic orientation-aware touching is definitionally the concrete periodic
physical-link touching relation. -/
@[simp] theorem z2PeriodicHypercubicOrientedWilsonSystem_touches_iff
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).PlaquetteTouchesEdge
        p e ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  rfl

/-- The orientation-aware active-neighbor finset agrees exactly with the
previously proved physical periodic active-neighbor finset. -/
theorem z2PeriodicHypercubicOrientedWilsonSystem_activeNeighbors_eq
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighbors
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) target =
      periodicHypercubicActiveNeighbors n target := by
  classical
  apply Finset.ext
  intro source
  rw [finite_oriented_mem_activePlaquetteNeighbors_iff,
    periodicHypercubic_mem_activeNeighbors_iff]
  simp only [z2PeriodicHypercubicOrientedWilsonSystem_touches_iff]

/-- The orientation-aware shared-plaquette finset agrees exactly with the
concrete periodic shared-plaquette finset. -/
theorem z2PeriodicHypercubicOrientedWilsonSystem_sharedPlaquettes_eq
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    FiniteOrientedLatticeWilsonSystem.sharedPlaquettes
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        target source =
      periodicHypercubicSharedPlaquettes n target source := by
  classical
  apply Finset.ext
  intro p
  rw [finite_oriented_mem_sharedPlaquettes_iff,
    periodicHypercubic_mem_sharedPlaquettes_iff]
  simp only [z2PeriodicHypercubicOrientedWilsonSystem_touches_iff]

/-- Incidence certificate for an orientation-correct four-dimensional Wilson
system. -/
structure FiniteOrientedWilsonFourDimensionalIncidenceCertificate
    (L : FiniteOrientedLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  activeNeighborCard_le_eighteen : ∀ target : L.Edge,
    (L.activePlaquetteNeighbors target).card ≤ 18
  activeSharedPlaquetteCard_le_one : ∀ (target source : L.Edge),
    source ∈ L.activePlaquetteNeighbors target →
      (L.sharedPlaquettes target source).card ≤ 1

/-- The periodic orientation-correct `Z₂` system satisfies the exact
four-dimensional incidence certificate for every side length at least three. -/
def z2PeriodicHypercubicOrientedIncidenceCertificate
    (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) :=
  { edgeCard_pos := by
      exact Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
    activeNeighborCard_le_eighteen := by
      intro target
      rw [z2PeriodicHypercubicOrientedWilsonSystem_activeNeighbors_eq]
      exact periodicHypercubicActiveNeighbors_card_le_eighteen n target
    activeSharedPlaquetteCard_le_one := by
      intro target source hActive
      have hNe : source ≠ target :=
        (finite_oriented_mem_activePlaquetteNeighbors_iff
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          target source).mp hActive |>.2
      rw [z2PeriodicHypercubicOrientedWilsonSystem_sharedPlaquettes_eq]
      exact periodicHypercubicSharedPlaquettes_card_le_one
        n hn target source hNe }

end

end MathlibAnalytic
end MGAP4D
