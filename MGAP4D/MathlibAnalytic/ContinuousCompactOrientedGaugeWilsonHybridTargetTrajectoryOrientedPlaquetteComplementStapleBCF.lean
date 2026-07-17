import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryWilsonMultiStapleBCF
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A target incidence in an oriented plaquette, together with the proof that
none of the other three boundary incidences uses the same physical target
link.  The four constructors retain the cyclic position of the target and
avoid imposing a global no-repeated-edge axiom on the ambient geometry. -/
inductive ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) where
  | at0
      (p : C.base.geometry.Plaquette)
      (h0 : (C.base.geometry.boundary p 0).edge = target)
      (h1 : (C.base.geometry.boundary p 1).edge ≠ target)
      (h2 : (C.base.geometry.boundary p 2).edge ≠ target)
      (h3 : (C.base.geometry.boundary p 3).edge ≠ target)
  | at1
      (p : C.base.geometry.Plaquette)
      (h0 : (C.base.geometry.boundary p 0).edge ≠ target)
      (h1 : (C.base.geometry.boundary p 1).edge = target)
      (h2 : (C.base.geometry.boundary p 2).edge ≠ target)
      (h3 : (C.base.geometry.boundary p 3).edge ≠ target)
  | at2
      (p : C.base.geometry.Plaquette)
      (h0 : (C.base.geometry.boundary p 0).edge ≠ target)
      (h1 : (C.base.geometry.boundary p 1).edge ≠ target)
      (h2 : (C.base.geometry.boundary p 2).edge = target)
      (h3 : (C.base.geometry.boundary p 3).edge ≠ target)
  | at3
      (p : C.base.geometry.Plaquette)
      (h0 : (C.base.geometry.boundary p 0).edge ≠ target)
      (h1 : (C.base.geometry.boundary p 1).edge ≠ target)
      (h2 : (C.base.geometry.boundary p 2).edge ≠ target)
      (h3 : (C.base.geometry.boundary p 3).edge = target)

/-- The plaquette selected by an isolated target incidence. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.plaquette
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target) :
    C.base.geometry.Plaquette :=
  match inc with
  | .at0 p _ _ _ _ => p
  | .at1 p _ _ _ _ => p
  | .at2 p _ _ _ _ => p
  | .at3 p _ _ _ _ => p

/-- Orientation with which the selected target incidence is traversed. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target) :
    FiniteBoundaryOrientation :=
  match inc with
  | .at0 p _ _ _ _ => (C.base.geometry.boundary p 0).orientation
  | .at1 p _ _ _ _ => (C.base.geometry.boundary p 1).orientation
  | .at2 p _ _ _ _ => (C.base.geometry.boundary p 2).orientation
  | .at3 p _ _ _ _ => (C.base.geometry.boundary p 3).orientation

/-- Cyclic ordered product of the three non-target signed boundary values,
starting immediately after the selected target incidence. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration) : C.base.Gauge :=
  match inc with
  | .at0 p _ _ _ _ =>
      C.base.stepValue A (C.base.geometry.boundary p 1) *
        C.base.stepValue A (C.base.geometry.boundary p 2) *
        C.base.stepValue A (C.base.geometry.boundary p 3)
  | .at1 p _ _ _ _ =>
      C.base.stepValue A (C.base.geometry.boundary p 2) *
        C.base.stepValue A (C.base.geometry.boundary p 3) *
        C.base.stepValue A (C.base.geometry.boundary p 0)
  | .at2 p _ _ _ _ =>
      C.base.stepValue A (C.base.geometry.boundary p 3) *
        C.base.stepValue A (C.base.geometry.boundary p 0) *
        C.base.stepValue A (C.base.geometry.boundary p 1)
  | .at3 p _ _ _ _ =>
      C.base.stepValue A (C.base.geometry.boundary p 0) *
        C.base.stepValue A (C.base.geometry.boundary p 1) *
        C.base.stepValue A (C.base.geometry.boundary p 2)

/-- Orientation-normalized three-link plaquette-complement staple. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration) : C.base.Gauge :=
  match inc.targetOrientation with
  | .forward => inc.rawComplement A
  | .backward => (inc.rawComplement A)⁻¹

/-- Replacing a physical link different from the underlying signed incidence
leaves that signed step value unchanged. -/
theorem continuous_compact_oriented_stepValue_replaceLink_of_edge_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (step : FiniteOrientedBoundaryStep C.base.geometry.Edge)
    (hStep : step.edge ≠ target) :
    C.base.stepValue (C.base.replaceLink A target g) step =
      C.base.stepValue A step := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue,
          CompactOrientedGaugeWilsonSystem.replaceLink, hStep]

/-- At the replaced physical target, a signed incidence contributes the
inserted value or its inverse according to traversal orientation. -/
theorem continuous_compact_oriented_stepValue_replaceLink_of_edge_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (step : FiniteOrientedBoundaryStep C.base.geometry.Edge)
    (hStep : step.edge = target) :
    C.base.stepValue (C.base.replaceLink A target g) step =
      match step.orientation with
      | .forward => g
      | .backward => g⁻¹ := by
  cases step with
  | mk edge orientation =>
      have hEdge : edge = target := hStep
      subst edge
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue,
          CompactOrientedGaugeWilsonSystem.replaceLink]

/-- The raw three-step complement is independent of target-link replacement. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_rawComplement_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration)
    (g : C.base.Gauge) :
    inc.rawComplement (C.base.replaceLink A target g) =
      inc.rawComplement A := by
  cases inc with
  | at0 p h0 h1 h2 h3 =>
      change
        C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 1) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 3) =
        C.base.stepValue A (C.base.geometry.boundary p 1) *
            C.base.stepValue A (C.base.geometry.boundary p 2) *
          C.base.stepValue A (C.base.geometry.boundary p 3)
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3]
  | at1 p h0 h1 h2 h3 =>
      change
        C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 3) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 0) =
        C.base.stepValue A (C.base.geometry.boundary p 2) *
            C.base.stepValue A (C.base.geometry.boundary p 3) *
          C.base.stepValue A (C.base.geometry.boundary p 0)
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0]
  | at2 p h0 h1 h2 h3 =>
      change
        C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 3) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 0) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 1) =
        C.base.stepValue A (C.base.geometry.boundary p 3) *
            C.base.stepValue A (C.base.geometry.boundary p 0) *
          C.base.stepValue A (C.base.geometry.boundary p 1)
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1]
  | at3 p h0 h1 h2 h3 =>
      change
        C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 0) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 1) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 2) =
        C.base.stepValue A (C.base.geometry.boundary p 0) *
            C.base.stepValue A (C.base.geometry.boundary p 1) *
          C.base.stepValue A (C.base.geometry.boundary p 2)
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2]

/-- The orientation-normalized complement staple is target-independent. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleValue_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration)
    (g : C.base.Gauge) :
    inc.stapleValue (C.base.replaceLink A target g) =
      inc.stapleValue A := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue
  rw [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_rawComplement_replaceLink
    C target inc A g]

/-- The cyclic three-step complement as an actual continuous map. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplementContinuousMap
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target) :
    ContinuousMap C.base.Configuration C.base.Gauge := by
  cases inc with
  | at0 p h0 h1 h2 h3 =>
      exact
        ⟨fun A =>
            C.base.stepValue A (C.base.geometry.boundary p 1) *
              C.base.stepValue A (C.base.geometry.boundary p 2) *
              C.base.stepValue A (C.base.geometry.boundary p 3),
          ((continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 1)).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 2))).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 3))⟩
  | at1 p h0 h1 h2 h3 =>
      exact
        ⟨fun A =>
            C.base.stepValue A (C.base.geometry.boundary p 2) *
              C.base.stepValue A (C.base.geometry.boundary p 3) *
              C.base.stepValue A (C.base.geometry.boundary p 0),
          ((continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 2)).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 3))).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 0))⟩
  | at2 p h0 h1 h2 h3 =>
      exact
        ⟨fun A =>
            C.base.stepValue A (C.base.geometry.boundary p 3) *
              C.base.stepValue A (C.base.geometry.boundary p 0) *
              C.base.stepValue A (C.base.geometry.boundary p 1),
          ((continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 3)).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 0))).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 1))⟩
  | at3 p h0 h1 h2 h3 =>
      exact
        ⟨fun A =>
            C.base.stepValue A (C.base.geometry.boundary p 0) *
              C.base.stepValue A (C.base.geometry.boundary p 1) *
              C.base.stepValue A (C.base.geometry.boundary p 2),
          ((continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 0)).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 1))).mul
            (continuous_compact_oriented_stepValue C
              (C.base.geometry.boundary p 2))⟩

@[simp]
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_rawComplementContinuousMap_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration) :
    inc.rawComplementContinuousMap A = inc.rawComplement A := by
  cases inc <;> rfl

/-- The orientation-normalized three-link complement staple as an actual
continuous map on compact configuration space. -/
def ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleContinuousMap
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {target : C.base.geometry.Edge}
    (inc : C.IsolatedTargetPlaquetteIncidence target) :
    ContinuousMap C.base.Configuration C.base.Gauge where
  toFun := inc.stapleValue
  continuous_toFun := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue
    cases hOrientation : inc.targetOrientation
    · simpa [hOrientation] using inc.rawComplementContinuousMap.continuous
    · simpa [hOrientation] using
        (continuous_inv.comp inc.rawComplementContinuousMap.continuous)

@[simp]
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleContinuousMap_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration) :
    inc.stapleContinuousMap A = inc.stapleValue A := by
  rfl

/-- A finite family of isolated plaquette-complement staples is a valid
PR #924 target-independent staple family. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleFamily_targetIndependent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (incidence : ι → C.IsolatedTargetPlaquetteIncidence target) :
    C.targetIndependentStapleFamilyBCF target
      (fun i => (incidence i).stapleContinuousMap) := by
  intro i A g
  exact continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleValue_replaceLink
    C target (incidence i) A g

/-- Conjugation invariance makes the energy of a two-factor product invariant
under cyclic exchange. -/
private theorem conjugationInvariant_energy_mul_cycle
    {G : Type*}
    [Group G]
    (energy : G → ℝ)
    (hConj : ∀ h g, energy (h * g * h⁻¹) = energy g)
    (a b : G) :
    energy (a * b) = energy (b * a) := by
  calc
    energy (a * b) = energy (a⁻¹ * (a * b) * (a⁻¹)⁻¹) := by
      symm
      exact hConj a⁻¹ (a * b)
    _ = energy (b * a) := by
      congr 1
      group

/-- Conjugation and inversion invariance convert a backward target incidence
into the same `g * staple` section form used by a forward incidence. -/
private theorem conjugationInversionInvariant_energy_inv_mul
    {G : Type*}
    [Group G]
    (energy : G → ℝ)
    (hConj : ∀ h g, energy (h * g * h⁻¹) = energy g)
    (hInv : ∀ g, energy g⁻¹ = energy g)
    (g r : G) :
    energy (g⁻¹ * r) = energy (g * r⁻¹) := by
  calc
    energy (g⁻¹ * r) = energy ((g⁻¹ * r)⁻¹) := by
      symm
      exact hInv (g⁻¹ * r)
    _ = energy (r⁻¹ * g) := by
      congr 1
      group
    _ = energy (g * r⁻¹) :=
      conjugationInvariant_energy_mul_cycle energy hConj r⁻¹ g

/-- Before orientation normalization, the plaquette energy of a target-updated
configuration is the energy of the inserted signed target value followed by
the cyclic three-step complement. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_energy_replaceLink_eq_targetFirst
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration)
    (g : C.base.Gauge) :
    C.base.plaquetteEnergy
        (C.base.plaquetteHolonomy
          (C.base.replaceLink A target g) inc.plaquette) =
      C.base.plaquetteEnergy
        ((match inc.targetOrientation with
          | .forward => g
          | .backward => g⁻¹) * inc.rawComplement A) := by
  cases inc with
  | at0 p h0 h1 h2 h3 =>
      change C.base.plaquetteEnergy
          (C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 0) *
              C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 1) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 3)) = _
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_eq C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3]
      cases hOrientation : (C.base.geometry.boundary p 0).orientation <;>
        simp [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc]
  | at1 p h0 h1 h2 h3 =>
      change C.base.plaquetteEnergy
          (C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 0) *
              C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 1) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 3)) = _
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_eq C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3]
      cases hOrientation : (C.base.geometry.boundary p 1).orientation
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0))
              (g * C.base.stepValue A (C.base.geometry.boundary p 2) *
                C.base.stepValue A (C.base.geometry.boundary p 3)))
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0))
              (g⁻¹ * C.base.stepValue A (C.base.geometry.boundary p 2) *
                C.base.stepValue A (C.base.geometry.boundary p 3)))
  | at2 p h0 h1 h2 h3 =>
      change C.base.plaquetteEnergy
          (C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 0) *
              C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 1) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 3)) = _
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_eq C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h3]
      cases hOrientation : (C.base.geometry.boundary p 2).orientation
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0) *
                C.base.stepValue A (C.base.geometry.boundary p 1))
              (g * C.base.stepValue A (C.base.geometry.boundary p 3)))
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0) *
                C.base.stepValue A (C.base.geometry.boundary p 1))
              (g⁻¹ * C.base.stepValue A (C.base.geometry.boundary p 3)))
  | at3 p h0 h1 h2 h3 =>
      change C.base.plaquetteEnergy
          (C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 0) *
              C.base.stepValue (C.base.replaceLink A target g)
                (C.base.geometry.boundary p 1) *
            C.base.stepValue (C.base.replaceLink A target g)
              (C.base.geometry.boundary p 2) *
          C.base.stepValue (C.base.replaceLink A target g)
            (C.base.geometry.boundary p 3)) = _
      rw [continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h0,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h1,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_ne C A target g _ h2,
        continuous_compact_oriented_stepValue_replaceLink_of_edge_eq C A target g _ h3]
      cases hOrientation : (C.base.geometry.boundary p 3).orientation
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0) *
                C.base.stepValue A (C.base.geometry.boundary p 1) *
                C.base.stepValue A (C.base.geometry.boundary p 2)) g)
      · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.targetOrientation,
          ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.rawComplement,
          hOrientation, mul_assoc] using
            (conjugationInvariant_energy_mul_cycle
              C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant
              (C.base.stepValue A (C.base.geometry.boundary p 0) *
                C.base.stepValue A (C.base.geometry.boundary p 1) *
                C.base.stepValue A (C.base.geometry.boundary p 2)) g⁻¹)

/-- Exact oriented plaquette-complement formula. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteIncidence_energy_replaceLink_eq_staple
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hInv : ∀ u : C.base.Gauge,
      C.base.plaquetteEnergy u⁻¹ = C.base.plaquetteEnergy u)
    (target : C.base.geometry.Edge)
    (inc : C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration)
    (g : C.base.Gauge) :
    C.base.plaquetteEnergy
        (C.base.plaquetteHolonomy
          (C.base.replaceLink A target g) inc.plaquette) =
      C.base.plaquetteEnergy (g * inc.stapleValue A) := by
  rw [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_energy_replaceLink_eq_targetFirst
    C target inc A g]
  cases hOrientation : inc.targetOrientation
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue,
      hOrientation]
  · simpa [ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.stapleValue,
      hOrientation] using
      (conjugationInversionInvariant_energy_inv_mul
        C.base.plaquetteEnergy C.base.plaquetteEnergy_conjInvariant hInv
        g (inc.rawComplement A))

/-- The continuous plaquette energy as an actual bounded continuous function on
the compact Gauge group. -/
def ContinuousCompactOrientedGaugeWilsonSystem.plaquetteEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    BoundedContinuousFunction C.base.Gauge ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨C.base.plaquetteEnergy, C.plaquetteEnergy_continuous⟩

@[simp]
theorem continuous_compact_oriented_plaquetteEnergyBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (g : C.base.Gauge) :
    C.plaquetteEnergyBCF g = C.base.plaquetteEnergy g := by
  rfl

/-- The actual configuration observable obtained by summing the Wilson energies
of a finite family of isolated target-touching plaquettes. -/
def ContinuousCompactOrientedGaugeWilsonSystem.isolatedTargetPlaquetteObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (incidence : ι → C.IsolatedTargetPlaquetteIncidence target) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  C.multiStapleCylinderObservableBCF target C.plaquetteEnergyBCF
    (fun i => (incidence i).stapleContinuousMap)

/-- After inserting a target value, the concrete multi-staple observable is
exactly the sum of the selected oriented plaquette energies. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_replaceLink_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (hInv : ∀ u : C.base.Gauge,
      C.base.plaquetteEnergy u⁻¹ = C.base.plaquetteEnergy u)
    (target : C.base.geometry.Edge)
    (incidence : ι → C.IsolatedTargetPlaquetteIncidence target)
    (A : C.base.Configuration)
    (g : C.base.Gauge) :
    C.isolatedTargetPlaquetteObservableBCF target incidence
        (C.base.replaceLink A target g) =
      ∑ i, C.base.plaquetteEnergy
        (C.base.plaquetteHolonomy
          (C.base.replaceLink A target g) (incidence i).plaquette) := by
  classical
  unfold ContinuousCompactOrientedGaugeWilsonSystem.isolatedTargetPlaquetteObservableBCF
  rw [continuous_compact_oriented_multiStapleCylinderObservableBCF_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [continuous_compact_oriented_plaquetteEnergyBCF_apply]
  rw [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleContinuousMap_apply]
  rw [compact_oriented_replaceLink_same]
  rw [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleValue_replaceLink
    C target (incidence i) A g]
  symm
  exact continuous_compact_oriented_isolatedTargetPlaquetteIncidence_energy_replaceLink_eq_staple
    C hInv target (incidence i) A g

/-- Exact endpoint oscillation margin for an actual finite family of oriented
plaquette-complement staples. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_oscillationMargin_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (incidence : ι → C.IsolatedTargetPlaquetteIncidence target)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target (C.isolatedTargetPlaquetteObservableBCF target incidence) z =
      abs
        (multiRightTranslateSumOscillationBCF C.plaquetteEnergyBCF
            (fun i => (incidence i).stapleValue
              (C.independentPairHybridConfiguration z.1 z.2 0)) -
          multiRightTranslateSumOscillationBCF C.plaquetteEnergyBCF
            (fun i => (incidence i).stapleValue
              (C.independentPairHybridConfiguration z.1 z.2
                (Fintype.card C.base.geometry.Edge)))) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.isolatedTargetPlaquetteObservableBCF
  simpa only [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleContinuousMap_apply] using
    (continuous_compact_oriented_multiStapleCylinderObservableBCF_oscillationMargin_eq
      C target C.plaquetteEnergyBCF
        (fun i => (incidence i).stapleContinuousMap)
        (continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleFamily_targetIndependent
          C target incidence) z)

/-- The coordinate-update witness for the actual selected plaquette observable
is exactly inequality of its two endpoint oriented-complement oscillations. -/
theorem continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_coordinateUpdateWitness_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {ι : Type*}
    [Fintype ι]
    (target : C.base.geometry.Edge)
    (incidence : ι → C.IsolatedTargetPlaquetteIncidence target)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target (C.isolatedTargetPlaquetteObservableBCF target incidence) z ↔
      multiRightTranslateSumOscillationBCF C.plaquetteEnergyBCF
          (fun i => (incidence i).stapleValue
            (C.independentPairHybridConfiguration z.1 z.2 0)) ≠
        multiRightTranslateSumOscillationBCF C.plaquetteEnergyBCF
          (fun i => (incidence i).stapleValue
            (C.independentPairHybridConfiguration z.1 z.2
              (Fintype.card C.base.geometry.Edge))) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.isolatedTargetPlaquetteObservableBCF
  simpa only [continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleContinuousMap_apply] using
    (continuous_compact_oriented_multiStapleCylinderObservableBCF_coordinateUpdateWitness_iff_oscillation_ne
      C target C.plaquetteEnergyBCF
        (fun i => (incidence i).stapleContinuousMap)
        (continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleFamily_targetIndependent
          C target incidence) z)

/-- The actual `SU(N)` continuous compact oriented Wilson system satisfies the
inversion-invariance hypothesis required by the backward-incidence formula. -/
theorem specialUnitaryContinuousCompactOrientedGaugeWilsonSystem_plaquetteEnergy_inv
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (U : SpecialUnitaryMatrixGroup N) :
    (specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
        geometry N hN beta beta_nonneg).base.plaquetteEnergy U⁻¹ =
      (specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
        geometry N hN beta beta_nonneg).base.plaquetteEnergy U := by
  simpa [specialUnitaryContinuousCompactOrientedGaugeWilsonSystem,
    specialUnitaryCompactOrientedGaugeWilsonSystem] using
    (specialUnitaryWilsonPlaquetteEnergy_inv (N := N) U)

end

end MathlibAnalytic
end MGAP4D
