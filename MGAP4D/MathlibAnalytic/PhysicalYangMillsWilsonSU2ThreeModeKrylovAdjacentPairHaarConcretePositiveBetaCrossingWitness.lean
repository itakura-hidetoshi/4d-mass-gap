import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarWilsonJointDiagonalMinor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryCrossingRightTargetLinkEnergyVariation
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import Mathlib.Tactic

/-!
# P4: a concrete positive-beta SU(2) Wilson temporal crossing witness

The literal even-periodic spatial slice always has a distinguished
time-zero spatial link e=(zero vertex, positive axis 1), including H=0.
Let A be the identity SU(2) configuration on that slice and let B
differ from A ONLY at e by the explicit rotation R(pi).

The exact one-link Wilson-action update theorem (no independence or
support hypothesis) and the explicit SU(2) Wilson energy formula give

  crossingAction(A,B) = E_W(R(pi)) = 2,

so the ORIGINAL physical temporal crossing kernel is exactly

  C_beta(A,B) = exp(-2*beta) < 1  for every beta>0.

Combined with PR #5294, the genuine full one-slab Wilson kernel
crossing minor is STRICTLY POSITIVE for these explicit two boundaries
for every positive coupling and every even periodic spatial extent.

This closes the previously OPEN existential strict off-diagonal
crossing-kernel witness. The pointwise physical top-vacuum
representative at this chosen A,B may be zero (it is an L2 quotient
representative!), so NO joint-density pointwise nonseparability or
a.e. posterior nonmeasurability is asserted without further work.
No Dobrushin, surrogate posterior, volume-uniform estimate,
or continuum Yang--Mills mass-gap inference.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4PositiveCrossingTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4PositiveCrossingCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4PositiveCrossingSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4PositiveCrossingMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4PositiveCrossingBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4PositiveCrossingSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A concrete positive-direction spatial link in every even-periodic
finite spatial slice. No assumed Nonempty or positive H is needed. -/
def originalWilsonExplicitSpatialTargetLink
    (H : ℕ) : PeriodicHypercubicEvenSpatialSliceLink H :=
  (⟨(fun _ => 0 : PeriodicHypercubicEvenVertex H), by
      rfl⟩,
    ⟨(1 : PeriodicHypercubicAxis), by decide⟩)

/-- The original SU(2) spatial-slice boundary configuration with
the group identity at every spatial link. -/
def originalWilsonExplicitIdentityBoundary
    (H : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun _ => 1

/-- A SECOND ACTUAL boundary configuration obtained from the first
by updating only the explicitly chosen right spatial link with R(pi). -/
def originalWilsonExplicitRotatedBoundary
    (H : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  Function.update (originalWilsonExplicitIdentityBoundary H)
    (originalWilsonExplicitSpatialTargetLink H)
    (specialUnitaryTwoRotation Real.pi)

/-- The original temporal crossing action of the identity boundary
with itself vanishes, because every local relative plaquette
holonomy is 1. -/
theorem originalWilsonExplicitIdentityBoundary_crossingAction_eq_zero
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
      H 2 (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitIdentityBoundary H) = 0 := by
  classical
  simp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction,
    originalWilsonExplicitIdentityBoundary,
    specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]

/-- The concrete SU(2) rotation through pi has Wilson plaquette
energy EXACTLY two, not merely a nonzero lower bound. -/
theorem originalWilsonExplicitPiRotation_energy_eq_two :
    specialUnitaryWilsonPlaquetteEnergy 2 (specialUnitaryTwoRotation Real.pi) = 2 := by
  rw [specialUnitaryWilsonPlaquetteEnergy_two_rotation, Real.cos_pi]
  norm_num

/-- One-link update cancels every other crossing-action contribution.
The original crossing action of the explicit two physical boundaries
is EXACTLY two at every finite spatial extent H. -/
theorem originalWilsonExplicitRotatedBoundary_crossingAction_eq_two
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
      H 2 (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H) = 2 := by
  let A := originalWilsonExplicitIdentityBoundary H
  let e := originalWilsonExplicitSpatialTargetLink H
  let g := specialUnitaryTwoRotation Real.pi
  have hzero :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A A = 0 :=
    originalWilsonExplicitIdentityBoundary_crossingAction_eq_zero H
  have hE : specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * g) = 2 := by
    simpa [A, originalWilsonExplicitIdentityBoundary, g] using
      originalWilsonExplicitPiRotation_energy_eq_two
  have hEzero :
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * A e) = 0 := by
    simpa [A, originalWilsonExplicitIdentityBoundary] using
      (specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num))
  have hUpdate :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_update_right_sub_eq
      H 2 A A e g
  change
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
        H 2 A (Function.update A e g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A A =
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * g) -
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * A e) at hUpdate
  rw [hzero, hE, hEzero] at hUpdate
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
      H 2 A (Function.update A e g) = 2
  linarith

/-- For any beta, the ORIGINAL temporal crossing kernel at the
explicit physical SU(2) boundary pair is the exact scalar exp(-2 beta). -/
theorem originalWilsonExplicitBoundaries_crossingKernel_eq_exp_neg_two_beta
    (H : ℕ) (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H) =
      Real.exp (-2 * beta) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann,
    originalWilsonExplicitRotatedBoundary_crossingAction_eq_two]
  congr 1
  ring

/-- The concrete crossing kernel is STRICTLY subunit for EVERY
positive Wilson beta, uniformly in the choice of finite H (although
its off-diagonal VALUE can approach 1 as beta tends to zero). -/
theorem originalWilsonExplicitBoundaries_crossingKernel_lt_one
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H) < 1 := by
  rw [originalWilsonExplicitBoundaries_crossingKernel_eq_exp_neg_two_beta]
  calc
    Real.exp (-2 * beta) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

/-- The actual positive-beta ONE-SLAB Wilson kernel crossing minor
has an EXPLICIT strictly positive finite-volume witness for EVERY H.
No physical vacuum representative has been evaluated at a null point. -/
theorem originalWilsonExplicitBoundaries_oneSlabKernelMinor_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 < originalWilsonTemporalKernelTwoByTwoMinor
      H 2 beta
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H)
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H) := by
  exact originalWilsonTemporalKernelTwoByTwoMinor_pos_of_crossing_lt_one_SU2
    H beta (le_of_lt hbeta) _ _
    (originalWilsonExplicitBoundaries_crossingKernel_lt_one H beta hbeta)

/-- Genuine existential strict crossing minor in every finite
physical SU(2) even-periodic spatial extent, including H=0. -/
theorem originalWilsonTemporalKernelTwoByTwoMinor_exists_positive_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      0 < originalWilsonTemporalKernelTwoByTwoMinor H 2 beta A B A B := by
  exact ⟨originalWilsonExplicitIdentityBoundary H,
    originalWilsonExplicitRotatedBoundary H,
    originalWilsonExplicitBoundaries_oneSlabKernelMinor_pos H beta hbeta⟩

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
