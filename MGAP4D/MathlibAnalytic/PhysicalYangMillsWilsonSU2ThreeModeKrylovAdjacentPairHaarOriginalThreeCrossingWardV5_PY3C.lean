import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteThreeCrossingOrthogonalityV5_PY3B
import Mathlib.Tactic

/-!
# P4-Q2-PY3C — original FULL temporal-crossing cube Haar Ward vanishes

PY3/PY3B establish from the REAL four-edge finite SU(2) lattice
geometry and a center flip that each spatial plaquette real trace
is orthogonal to ANY triple of true temporal-crossing link energies.

The original complete crossing action is the finite sum over every
spatial link, so its cube is the exact triple sum, including ALL
coincident indices, all diagonal terms and all mixed terms.
Continuous compact-Haar integrability and Mathlib's finite sum
integral identity lift PY3B term by term without posterior substitution.

Using PW2's exact centered first-action trace sum, the actual
THREE-crossing centered Haar Ward profile also vanishes exactly.
This is an unconditional selection rule in the original SU(2)
reference Haar; it does not by itself assert fifth Wilson coefficient
nonvanishing, vanishing, or third Hankel positivity.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY3C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY3C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY3C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY3C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY3C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PY3C_nativeFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection

local instance p4Q2PY3C_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalFullThreeCrossingHaar
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- The full original temporal Wilson crossing C(X,B), cubed, is
orthogonal to ANY true spatial Wilson plaquette character under
the unmodified finite spatial SU(2) Haar measure. -/
theorem p4Q2PY3_originalPlaquetteChar_crossingCubeHaar_zero
    (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, χ p A * (Cross A B) ^ 3 ∂haar) = 0 := by
  classical
  let T : Link → Cfg → ℝ := fun e A =>
    E ((A e)⁻¹ * B e)
  have hChi : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hT (e : Link) : Continuous (T e) := by
    change Continuous (fun A : Cfg => E ((A e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f g : Link) :
      Integrable (fun A : Cfg =>
        χ p A * (T e A * T f A * T g A)) haar :=
    (hChi.mul (((hT e).mul (hT f)).mul (hT g)))
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInnerCont (e f : Link) :
      Continuous (fun A : Cfg =>
        ∑ g : Link, χ p A * (T e A * T f A * T g A)) := by
    apply continuous_finset_sum
    intro g _hg
    exact hChi.mul (((hT e).mul (hT f)).mul (hT g))
  have hMiddleCont (e : Link) :
      Continuous (fun A : Cfg =>
        ∑ f : Link, ∑ g : Link,
          χ p A * (T e A * T f A * T g A)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hInnerCont e f
  have hTripleIntegral :
      (∫ A : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          χ p A * (T e A * T f A * T g A) ∂haar) =
      ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ A : Cfg,
          χ p A * (T e A * T f A * T g A) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hMiddleCont e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ =>
      (hInnerCont e f).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [integral_finset_sum _ (fun g _ => hEach e f g)]
  have hCube (A : Cfg) :
      (∑ e : Link, T e A) ^ 3 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A * T f A * T g A := by
    have hSquare :
        (∑ e : Link, T e A) * (∑ f : Link, T f A) =
          ∑ e : Link, ∑ f : Link, T e A * T f A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    calc
      (∑ e : Link, T e A) ^ 3 =
          ((∑ e : Link, T e A) * (∑ f : Link, T f A)) *
            (∑ g : Link, T g A) := by ring
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
            T e A * T f A * T g A := by
        rw [hSquare, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [Finset.mul_sum]
  have hPoint (A : Cfg) :
      χ p A * (∑ e : Link, T e A) ^ 3 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          χ p A * (T e A * T f A * T g A) := by
    rw [hCube, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [Finset.mul_sum]
  have hEachZero (e f g : Link) :
      (∫ A : Cfg,
        χ p A * (T e A * T f A * T g A) ∂haar) = 0 :=
    p4Q2PY3_originalPlaquette_threeCrossingHaar_zero H p e f g B
  calc
    (∫ A : Cfg, χ p A * (Cross A B) ^ 3 ∂haar) =
        ∫ A : Cfg,
          ∑ e : Link, ∑ f : Link, ∑ g : Link,
            χ p A * (T e A * T f A * T g A) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
      exact hPoint A
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ A : Cfg, χ p A * (T e A * T f A * T g A) ∂haar) :=
      hTripleIntegral
    _ = 0 := by simp [hEachZero]

/-- A true centered three-crossing Haar Ward profile formed with
the ORIGINAL first-moment spatial plaquette variation. -/
noncomputable def p4Q2PY3_originalThreeCrossingCenteredHaar
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, (Cross A B) ^ 3 * h A ∂haar

/-- There is NO three-crossing spatial plaquette contribution in the
original fifth-Ward Haar sector, because four genuine plaquette
edges cannot be covered by three crossings. -/
theorem p4Q2PY3_originalThreeCrossingCenteredHaar_zero (B : Cfg) :
    p4Q2PY3_originalThreeCrossingCenteredHaar H B = 0 := by
  classical
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hInt (p : Plaq) :
      Integrable (fun A : Cfg =>
        χ p A * (Cross A B) ^ 3) haar :=
    ((p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      (hCross.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      (Cross A B) ^ 3 * ((1 / 2 : ℝ) * Φ A) =
        (1 / 2 : ℝ) *
          (∑ p : Plaq, χ p A * (Cross A B) ^ 3) := by
    calc
      (Cross A B) ^ 3 * ((1 / 2 : ℝ) * Φ A) =
          (1 / 2 : ℝ) *
            ((∑ p : Plaq, χ p A) * (Cross A B) ^ 3) := by
        unfold p4Q2PW2_originalAllPlaquetteRealTrace
        ring
      _ = (1 / 2 : ℝ) *
            (∑ p : Plaq, χ p A * (Cross A B) ^ 3) := by
        rw [Finset.sum_mul]
  change (∫ A : Cfg, (Cross A B) ^ 3 * h A ∂haar) = 0
  calc
    (∫ A : Cfg, (Cross A B) ^ 3 * h A ∂haar) =
        ∫ A : Cfg, (1 / 2 : ℝ) *
          (∑ p : Plaq, χ p A * (Cross A B) ^ 3) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
      exact hPoint A
    _ = (1 / 2 : ℝ) *
        (∫ A : Cfg,
          ∑ p : Plaq, χ p A * (Cross A B) ^ 3 ∂haar) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) *
        (∑ p : Plaq,
          (∫ A : Cfg, χ p A * (Cross A B) ^ 3 ∂haar)) := by
      rw [integral_finset_sum _ (fun p _ => hInt p)]
    _ = 0 := by
      simp [p4Q2PY3_originalPlaquetteChar_crossingCubeHaar_zero H]

end OriginalFullThreeCrossingHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalPlaquetteChar_crossingCubeHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalThreeCrossingCenteredHaar_zero
