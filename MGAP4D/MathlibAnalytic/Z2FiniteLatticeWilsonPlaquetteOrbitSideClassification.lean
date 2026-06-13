import MGAP4D.MathlibAnalytic.Z2FiniteInvolutiveEdgeOrbitAssembly
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteSideClassification
import Mathlib.Data.Fintype.EquivFin

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A finite plaquette carrier equipped with an involution and a finite rank.
The lower-ranked member of a nontrivial reflection orbit is positive, the
higher-ranked member is negative, and fixed plaquettes are crossing-plane
plaquettes. -/
structure FiniteInvolutivePlaquetteOrbitPartition
    (Plaquette : Type) [Fintype Plaquette] where
  reflection : Plaquette → Plaquette
  reflection_involutive : Function.Involutive reflection
  rank : Plaquette ≃ Fin (Fintype.card Plaquette)

/-- Reflection-side classifier generated from finite plaquette orbits. -/
def FiniteInvolutivePlaquetteOrbitPartition.side
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette)
    (p : Plaquette) : ReflectionPlaquetteSide :=
  if P.rank p < P.rank (P.reflection p) then
    .positive
  else if P.rank (P.reflection p) < P.rank p then
    .negative
  else
    .crossing

/-- Reflection exchanges positive and negative plaquettes and preserves the
crossing-plane sector. -/
@[simp]
theorem FiniteInvolutivePlaquetteOrbitPartition.side_reflection
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette)
    (p : Plaquette) :
    P.side (P.reflection p) =
      match P.side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  by_cases hlt : P.rank p < P.rank (P.reflection p)
  · have hnot : ¬ P.rank (P.reflection p) < P.rank p :=
      not_lt_of_ge hlt.le
    simp [FiniteInvolutivePlaquetteOrbitPartition.side,
      P.reflection_involutive p, hlt, hnot]
  · by_cases hgt : P.rank (P.reflection p) < P.rank p
    · simp [FiniteInvolutivePlaquetteOrbitPartition.side,
        P.reflection_involutive p, hlt, hgt]
    · have heq : P.rank p = P.rank (P.reflection p) :=
        le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      simp [FiniteInvolutivePlaquetteOrbitPartition.side,
        P.reflection_involutive p, hlt, hgt, heq]

/-- Positive plaquettes selected by the orbit classifier. -/
def FiniteInvolutivePlaquetteOrbitPartition.positivePlaquettes
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette) :
    List Plaquette :=
  Finset.univ.toList.filter fun p => P.side p = .positive

/-- Crossing-plane plaquettes selected by the orbit classifier. -/
def FiniteInvolutivePlaquetteOrbitPartition.crossingPlaquettes
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette) :
    List Plaquette :=
  Finset.univ.toList.filter fun p => P.side p = .crossing

/-- Negative plaquettes selected by the orbit classifier. -/
def FiniteInvolutivePlaquetteOrbitPartition.negativePlaquettes
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette) :
    List Plaquette :=
  Finset.univ.toList.filter fun p => P.side p = .negative

/-- The orbit-generated three sectors enumerate every plaquette exactly once,
up to permutation. -/
theorem FiniteInvolutivePlaquetteOrbitPartition.index_perm
    {Plaquette : Type} [Fintype Plaquette]
    (P : FiniteInvolutivePlaquetteOrbitPartition Plaquette) :
    List.Perm
      (Finset.univ.toList : List Plaquette)
      (P.positivePlaquettes ++ P.crossingPlaquettes ++
        P.negativePlaquettes) := by
  simpa [FiniteInvolutivePlaquetteOrbitPartition.positivePlaquettes,
    FiniteInvolutivePlaquetteOrbitPartition.crossingPlaquettes,
    FiniteInvolutivePlaquetteOrbitPartition.negativePlaquettes] using
      list_perm_three_side_partition P.side Finset.univ.toList

/-- Reflection-orbit data plus the three local energy identities.  Unlike the
lower-level index partition, the three plaquette lists are generated
automatically from the involution. -/
structure Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification
    (L : FiniteLatticeWilsonSystem) where
  configurationEquiv : L.Configuration ≃ (L.Edge → Z2Gauge)
  edgeOrbit : FiniteInvolutiveEdgeOrbitPartition L.Edge
  plaquetteOrbit : FiniteInvolutivePlaquetteOrbitPartition L.Plaquette
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables :
    List (edgeOrbit.PositiveConfiguration → Z2Gauge)
  positiveEnergyTerms :
    edgeOrbit.PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteOrbit.side p = .positive).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteOrbit.side p = .crossing).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteOrbit.side p = .negative).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms y

/-- Assemble two orbit-half configurations into the Wilson configuration
carrier. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.assemble
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L)
    (x y : C.edgeOrbit.PositiveConfiguration) : L.Configuration :=
  C.configurationEquiv.symm (C.edgeOrbit.assemble x y)

/-- Transport the edge-orbit reflection to the Wilson configuration carrier. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.reflection
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L)
    (A : L.Configuration) : L.Configuration :=
  C.configurationEquiv.symm
    (C.edgeOrbit.configurationReflection (C.configurationEquiv A))

/-- The transported reflection is involutive. -/
theorem Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.reflection_involutive
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L) :
    Function.Involutive C.reflection := by
  intro A
  apply C.configurationEquiv.injective
  simp [Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.reflection,
    C.edgeOrbit.configurationReflection_involutive]

/-- Reflection exchanges the two assembled half-configurations. -/
theorem Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.reflection_assemble
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L)
    (x y : C.edgeOrbit.PositiveConfiguration) :
    C.reflection (C.assemble x y) = C.assemble y x := by
  apply C.configurationEquiv.injective
  simpa [Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.reflection,
    Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.assemble] using
      C.edgeOrbit.reflection_assemble x y

/-- Convert reflection-orbit geometry into the existing side-classification
interface consumed by the finite-volume OS theorem. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification.toSideClassification
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L) :
    Z2FiniteLatticeWilsonPlaquetteSideClassification L :=
  { PositiveConfiguration := C.edgeOrbit.PositiveConfiguration
    assemble := C.assemble
    reflection := C.reflection
    reflection_involutive := C.reflection_involutive
    reflection_assemble := C.reflection_assemble
    energyIdentity := C.energyIdentity
    energyNontrivial := C.energyNontrivial
    energy_order := C.energy_order
    crossingVariables := C.crossingVariables
    side := C.plaquetteOrbit.side
    positiveEnergyTerms := C.positiveEnergyTerms
    positive_terms_eq := C.positive_terms_eq
    crossing_terms_eq := C.crossing_terms_eq
    negative_terms_eq := C.negative_terms_eq }

/-- Reflection-orbit side data and the three local energy identities imply the
complete finite-volume OS reflection-positivity theorem. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_plaquetteOrbitSideClassification
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification L) :
    FiniteLatticeWilsonOSReflectionPositive
      C.toSideClassification.toIndexPartition.toTermPartition.toActionDecomposition.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive_of_sideClassification
    C.toSideClassification

end

end MathlibAnalytic
end MGAP4D
