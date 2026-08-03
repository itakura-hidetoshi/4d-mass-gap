import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualGaugeOneSlabKernelInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite temporal-link field across one geometric slab.  Its carrier is the
same finite vertex-function group that appears as the residual gauge group on a
spatial boundary slice. -/
abbrev FiniteEvenFourTorusZ2TemporalLinkField (H : ℕ) : Type :=
  FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H

/-- Unfixed-gauge temporal plaquette holonomy at one spatial link. -/
def finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : Z2Gauge :=
  (A e)⁻¹ * U e.1 * B e *
    (U (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹

/-- The temporal-link holonomy is the temporal-gauge relative link after the
upper boundary is transformed by the temporal-link field. -/
theorem finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_relative_smul
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e =
      (A e)⁻¹ * (U • B) e := by
  rw [finiteEvenFourTorusZ2ResidualSlice_smul_apply]
  simp [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy, mul_assoc]

/-- The identity temporal-link field recovers temporal gauge. -/
theorem finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_one
    (H : ℕ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
        H (1 : FiniteEvenFourTorusZ2TemporalLinkField H) A B e =
      (A e)⁻¹ * B e := by
  rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_relative_smul]
  simp

/-- Temporal crossing action before imposing temporal gauge. -/
def finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
    (H : ℕ)
    (_β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Finset.univ.toList.map fun e : FiniteEvenFourTorusSpatialLink H =>
    if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
    then energyIdentity
    else energyNontrivial).sum

/-- Exact reduction of the unfixed crossing action to the temporal-gauge action
with a transformed upper boundary. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_temporalGauge_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B =
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial A (U • B) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  simp_rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_relative_smul]

/-- Identity temporal links specialize the unfixed crossing action to temporal
gauge exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial
        (1 : FiniteEvenFourTorusZ2TemporalLinkField H) A B =
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial A B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_temporalGauge_smul]
  simp

/-- Symmetric full one-slab Wilson action with arbitrary temporal links. -/
def finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A +
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H β energyIdentity energyNontrivial U A B +
    (1 / 2 : ℝ) *
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial B

/-- The unfixed one-slab action is exactly a temporal-gauge action with the
upper boundary transformed by the temporal-link field. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H β energyIdentity energyNontrivial U A B =
      finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        H β energyIdentity energyNontrivial A (U • B) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_temporalGauge_smul,
    finiteEvenFourTorusZ2SpatialWilsonAction_smul]

/-- Identity temporal links recover the temporal-gauge full one-slab action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H β energyIdentity energyNontrivial
        (1 : FiniteEvenFourTorusZ2TemporalLinkField H) A B =
      finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        H β energyIdentity energyNontrivial A B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]
  simp

end

end MathlibAnalytic
end MGAP4D
