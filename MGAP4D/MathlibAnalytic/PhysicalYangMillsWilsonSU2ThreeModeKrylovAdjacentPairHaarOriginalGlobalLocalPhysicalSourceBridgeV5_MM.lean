import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGISpatialCoreTailObstructionV5_ML
import Mathlib.Tactic

/-!
# P4-Q2-MM — genuine original global/local Wilson Gauss-law source identity

ML split the *original* local GI determinant-square energy Q into an
arbitrary genuine spatial plaquette core and its actual outside energy.
The Q identity alone does not connect p-dependent genuine Hilbert
sources to one global source.

Here we prove an exact source-level identity in the ORIGINAL physical
Gauss-law Hilbert space at each finite spatial H:

  W_H U = ∑_{p ∈ P_H} W_{H,p} U.

The left side is the original JU spatial Wilson multiplication source;
each summand is LO's actual gauge-invariant Wilson plaquette
multiplication source. The equality holds as PHYSICAL Hilbert vectors
via their existing original Haar-L² representatives and mathlib's
linearity of ContinuousMap.toLp. It is not only a formal equality of
observables or a synthetic source synthesis.

Consequences for every ACTUAL original interacting Wilson posterior
signed physical GI response:
* global spatial physical GI = sum of genuine local physical GI;
* for any actual finite plaquette core S, the global physical source
  and its GI response split EXACTLY into core + outside tail;
* the error in GI response from truncating the global physical source
  to S is the true original signed response sum on its complement;
* the authentic two-coordinate global physical source xU+yW_H U
  has an exact unit-plus-local-response formula at the SAME original
  interacting posterior, with no duplicate unit source.

No property of the fine-coupling endpoint Krylov source synthesis is
asserted: equality of global spatial source with the p-family at a
FIXED finite spatial H is not an intertwining across H or r.
No volume-uniform remainder bound, artificial rank, Dobrushin,
independent-Haar posterior substitution, axiom, sorry, or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "W" => p4Q2JU_originalSpatialWilsonPhysicalSource H
local notation "Wp" => p4Q2LO_originalLocalPlaquettePhysicalSource H
local notation "GI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

/-- The literal original *continuous* Wilson spatial observable
equals its sum over the TRUE finite spatial plaquette type. This
converts LO's original physical list representation to the same
Fintype carrier used in LY–ML, with no new source or distribution. -/
theorem p4Q2MM_originalSpatialWilsonContinuous_eq_localFinsetSum :
    p4Q2JI_actualSpatialWilsonContinuous H =
      ∑ p : Plaq, p4Q2LO_originalLocalPlaquetteContinuous H p := by
  rw [p4Q2LO_originalSpatialWilsonContinuous_eq_localSum H]
  change (((Finset.univ : Finset Plaq).toList.map fun p =>
    p4Q2LO_originalLocalPlaquetteContinuous H p).sum) =
      ∑ p : Plaq, p4Q2LO_originalLocalPlaquetteContinuous H p
  exact Finset.sum_map_toList (Finset.univ : Finset Plaq)
    (p4Q2LO_originalLocalPlaquetteContinuous H)

/-- Stronger physical source identity: the original spatial Wilson
multiplication of the true physical unit equals the sum of genuine
single-plaquette multiplication sources *inside the Gauss-law Hilbert
submodule itself*. This is NOT an assumed intertwining. -/
theorem p4Q2MM_originalSpatialWilsonPhysicalSource_eq_sum_local :
    W = ∑ p : Plaq, Wp p := by
  classical
  apply Subtype.ext
  change ((W : Phys) : Lp ℝ 2 haar) =
    ((∑ p : Plaq, Wp p : Phys) : Lp ℝ 2 haar)
  rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp,
    p4Q2MM_originalSpatialWilsonContinuous_eq_localFinsetSum]
  simp only [Submodule.coe_sum,
    p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp,
    map_sum]

/-- True exact physical Hilbert core/outside decomposition on ANY
subset S of actual SU(2) spatial Wilson plaquettes. -/
theorem p4Q2MM_originalSpatialWilsonPhysicalSource_eq_core_add_outside
    (S : Finset Plaq) :
    W =
      (∑ p ∈ S, Wp p) +
      (∑ p ∈ (Finset.univ : Finset Plaq) \ S, Wp p) := by
  classical
  rw [p4Q2MM_originalSpatialWilsonPhysicalSource_eq_sum_local H]
  have hsplit :=
    Finset.sum_sdiff
      (s₁ := S) (s₂ := (Finset.univ : Finset Plaq))
      (f := fun p : Plaq => Wp p)
      (Finset.subset_univ S)
  calc
    (∑ p : Plaq, Wp p) =
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S, Wp p) +
        (∑ p ∈ S, Wp p) := hsplit.symm
    _ = (∑ p ∈ S, Wp p) +
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S, Wp p) := add_comm _ _

/-- Exact SUM of original interacting-Wilson signed GI responses
of real Gauss-law local plaquette sources, equal to the true
global spatial Wilson Hilbert source response. -/
theorem p4Q2MM_originalPhysicalGI_global_eq_localResponseSum
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    GI b hb W e z =
      ∑ p : Plaq, GI b hb (Wp p) e z := by
  rw [← p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI H b hb e z]
  rw [p4Q2MM_originalSpatialWilsonContinuous_eq_localFinsetSum H]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI H b hb e z p

/-- Finite-H exact original interacting-posterior physical GI
receiver core/tail decomposition, without ever replacing the
actual signed physical receiver or its Gauss-law source. -/
theorem p4Q2MM_originalPhysicalGI_global_eq_core_add_outside
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (S : Finset Plaq) :
    GI b hb W e z =
      (∑ p ∈ S, GI b hb (Wp p) e z) +
      (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
        GI b hb (Wp p) e z) := by
  rw [p4Q2MM_originalPhysicalGI_global_eq_localResponseSum H b hb e z]
  have hsplit :=
    Finset.sum_sdiff
      (s₁ := S) (s₂ := (Finset.univ : Finset Plaq))
      (f := fun p : Plaq => GI b hb (Wp p) e z)
      (Finset.subset_univ S)
  calc
    (∑ p : Plaq, GI b hb (Wp p) e z) =
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          GI b hb (Wp p) e z) +
        (∑ p ∈ S, GI b hb (Wp p) e z) := hsplit.symm
    _ = (∑ p ∈ S, GI b hb (Wp p) e z) +
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          GI b hb (Wp p) e z) := add_comm _ _

/-- The exact original physical GI truncation error is the
actual outside signed source response. No uniform bound on the
remainder has been assumed or established. -/
theorem p4Q2MM_originalPhysicalGI_core_truncation_error_exact
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (S : Finset Plaq) :
    GI b hb W e z -
      (∑ p ∈ S, GI b hb (Wp p) e z) =
        ∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          GI b hb (Wp p) e z := by
  have h := p4Q2MM_originalPhysicalGI_global_eq_core_add_outside
    H b hb e z S
  linarith

/-- The *same* authentic global Gauss-law source xU+yW_HU of LN
has a physical signed-GI expansion into a SINGLE unit contribution
and all genuine p-local Wilson physical contributions. The unit
source is not repeated per plaquette. -/
theorem p4Q2MM_originalGlobalTwoSourceGI_eq_unit_add_local
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (x y : ℝ) :
    GI b hb (p4Q2LN_originalPhysicalTwoSource H x y) e z =
      x * GI b hb U e z +
        y * (∑ p : Plaq, GI b hb (Wp p) e z) := by
  rw [p4Q2LN_originalPhysicalTwoSource_GI_eq H b hb e z x y,
    p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e z,
    p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI H b hb e z,
    p4Q2MM_originalPhysicalGI_global_eq_localResponseSum H b hb e z]

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalSpatialWilsonContinuous_eq_localFinsetSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalSpatialWilsonPhysicalSource_eq_sum_local
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalSpatialWilsonPhysicalSource_eq_core_add_outside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalPhysicalGI_global_eq_localResponseSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalPhysicalGI_global_eq_core_add_outside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalPhysicalGI_core_truncation_error_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MM_originalGlobalTwoSourceGI_eq_unit_add_local
