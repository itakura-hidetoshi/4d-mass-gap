import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteBoundaryHaarL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- The naturally oriented four-edge plaquette word `a b c⁻¹ d⁻¹`. -/
def orientedFourEdgePlaquetteWord
    {G : Type u} [Group G]
    (x : Fin 4 → G) : G :=
  x 0 * x 1 * (x 2)⁻¹ * (x 3)⁻¹

/-- The cyclic Haar representative is the conjugate of the naturally oriented
four-edge plaquette word by the first two forward edges.

Equivalently, the physical word `a b c⁻¹ d⁻¹` is the conjugate of
`c⁻¹ d⁻¹ a b` by `a b`. -/
theorem orientedFourEdgePlaquetteWord_eq_conj_cyclic
    {G : Type u} [Group G]
    (a b c d : G) :
    a * b * c⁻¹ * d⁻¹ =
      (a * b) * (c⁻¹ * d⁻¹ * a * b) * (a * b)⁻¹ := by
  group

/-- The `Fin 4` cyclic Haar word introduced in the previous package is exactly
`x₂⁻¹ x₃⁻¹ x₀ x₁` in the natural plaquette-edge order. -/
theorem haarFinFourCyclicPlaquetteWord_eq
    {G : Type u} [MeasurableSpace G] [Group G]
    (x : Fin 4 → G) :
    haarFinFourCyclicPlaquetteWord x =
      (x 2)⁻¹ * (x 3)⁻¹ * x 0 * x 1 := by
  simp [haarFinFourCyclicPlaquetteWord,
    haarFinFourCyclicNestedCoordinates,
    haarCyclicPlaquetteWord]

/-- The natural oriented `Fin 4` word is conjugate to the exact cyclic Haar
word already used by the boundary `L²` isometry. -/
theorem orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord
    {G : Type u} [MeasurableSpace G] [Group G]
    (x : Fin 4 → G) :
    orientedFourEdgePlaquetteWord x =
      (x 0 * x 1) * haarFinFourCyclicPlaquetteWord x *
        (x 0 * x 1)⁻¹ := by
  rw [haarFinFourCyclicPlaquetteWord_eq]
  exact orientedFourEdgePlaquetteWord_eq_conj_cyclic
    (x 0) (x 1) (x 2) (x 3)

/-- Wilson plaquette energy therefore cannot distinguish the natural oriented
word from the cyclic Haar representative. -/
theorem specialUnitaryWilsonPlaquetteEnergy_orientedFourEdge_eq_cyclic
    {N : ℕ}
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N (orientedFourEdgePlaquetteWord x) =
      specialUnitaryWilsonPlaquetteEnergy N
        (haarFinFourCyclicPlaquetteWord x) := by
  rw [orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord]
  exact specialUnitaryWilsonPlaquetteEnergy_conjInvariant
    (x 0 * x 1) (haarFinFourCyclicPlaquetteWord x)

/-- The actual oriented Wilson holonomy of the canonical primary spatial
plaquette, expressed directly in its four physical positive edge values. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge
    (H : ℕ)
    {G : Type u} [Group G]
    (A : PeriodicHypercubicEvenEdge H → G) :
    periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquette H) =
      orientedFourEdgePlaquetteWord
        (fun k => A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k)) := by
  rfl

/-- Restricting a full configuration to the reflection-fixed boundary retains
all four canonical primary spatial plaquette edge values exactly. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryRestriction_apply
    (H : ℕ)
    {Value : Type u}
    (A : PeriodicHypercubicEvenEdge H → Value)
    (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k) =
      A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k) :=
  rfl

/-- The actual Wilson holonomy of the canonical primary spatial plaquette is
conjugate to the cyclic holonomy read from its actual boundary restriction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_conj_boundaryCyclicHolonomy
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquette H) =
      let b :=
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A
      let h :=
        A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0) *
          A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 1)
      h * periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
          H N b * h⁻¹ := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge]
  rw [orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord]
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryRestriction_apply]

/-- Consequently the standard `SU(N)` Wilson plaquette energy of the actual
canonical primary spatial plaquette is exactly the class function of the
normalized-Haar cyclic boundary holonomy constructed in the previous package. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergy_eq_boundaryCyclicHolonomy
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_conj_boundaryCyclicHolonomy]
  exact specialUnitaryWilsonPlaquetteEnergy_conjInvariant
    (A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 0) *
      A (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H 1))
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
      H N
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A))

end

end MathlibAnalytic
end MGAP4D
