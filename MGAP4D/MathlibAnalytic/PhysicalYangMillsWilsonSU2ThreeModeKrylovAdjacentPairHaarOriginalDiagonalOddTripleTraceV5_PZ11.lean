import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullTripleCrossingDiagonalV5_PZ10
import Mathlib.Tactic

/-!
# P4-Q2-PZ11 — genuine Haar center-even / odd-three-trace selection

For a continuous center-even observable F on the ORIGINAL SU(2)
spatial product Haar space and ANY three genuine temporal crossing
link REAL traces tau_e(A,B) = 1 - E(A_e^{-1} B_e),
the full Haar integral of F tau_e tau_f tau_g is ZERO.

The proof does NOT presume three distinct temporal links: every
triple of link indices has an odd-multiplicity link, and the
actual single-link SU(2) center-flip changes that trace sign,
preserving any center-even F and the genuine product Haar measure.

Applied to the true four-edge plaquette character square chi_p^2,
this supplies the odd third-temporal-trace Ward selection on the
diagonal sector left by PZ10. It is a physical Haar selection
identity, NOT a statement about the entire W6 or mass gap.
No new axiom/sorry/admit, Wilson action change or posterior proxy.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ11_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ11_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ11_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ11_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ11_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalEvenOddTripleTrace

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H

/-- An abstract center-EVEN CONTINUOUS observable on the actual
spatial SU(2) configuration space is Haar orthogonal to an ODD
triple of genuine temporal REAL link traces, even with repetitions. -/
theorem p4Q2PZ11_centerEven_originalThreeTemporalTracesHaar_zero
    (F : C(Cfg, ℝ))
    (hEven : ∀ (target : Link) (A : Cfg),
      F (Flip target A) = F A)
    (e f g : Link) (B : Cfg) :
    (∫ A : Cfg, F A *
      ((1 - E ((A e)⁻¹ * B e)) *
        (1 - E ((A f)⁻¹ * B f)) *
        (1 - E ((A g)⁻¹ * B g))) ∂haar) = 0 := by
  let T : Link → Cfg → ℝ := fun d A => 1 - E ((A d)⁻¹ * B d)
  let obs : Cfg → ℝ := fun A =>
    F A * (T e A * T f A * T g A)
  have hT (d : Link) : Continuous (T d) := by
    dsimp [T]
    exact continuous_const.sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        ((continuous_apply d).inv.mul continuous_const))
  have hObs : Continuous obs :=
    F.continuous.mul (((hT e).mul (hT f)).mul (hT g))
  have hTflip (target d : Link) (A : Cfg) :
      T d (Flip target A) =
        if target = d then -(T d A) else T d A := by
    by_cases htd : target = d
    · subst d
      simpa only [if_pos rfl] using
        (p4Q2PY7_originalTemporalLinkTrace_centerOdd H target A B)
    · simp only [if_neg htd]
      dsimp [T]
      rw [p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target d (Ne.symm htd) A B]
  have hIndex : ∃ target : Link,
      (target = e ∧ target ≠ f ∧ target ≠ g) ∨
      (target = f ∧ target ≠ e ∧ target ≠ g) ∨
      (target = g ∧ target ≠ e ∧ target ≠ f) ∨
      (target = e ∧ target = f ∧ target = g) := by
    by_cases hef : e = f
    · by_cases heg : e = g
      · exact ⟨e, Or.inr (Or.inr (Or.inr ⟨rfl, hef, heg⟩))⟩
      · refine ⟨g, Or.inr (Or.inr (Or.inl ⟨rfl, Ne.symm heg, ?_⟩))⟩
        intro hgf
        exact heg (hef.trans hgf.symm)
    · by_cases heg : e = g
      · refine ⟨f, Or.inr (Or.inl ⟨rfl, Ne.symm hef, ?_⟩)⟩
        intro hfg
        exact hef (heg.trans hfg.symm)
      · exact ⟨e, Or.inl ⟨rfl, hef, heg⟩⟩
  obtain ⟨target, hIndex⟩ := hIndex
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    change
      F (Flip target A) *
        (T e (Flip target A) *
          T f (Flip target A) *
          T g (Flip target A)) =
      -(F A * (T e A * T f A * T g A))
    rw [hEven target A, hTflip target e A,
      hTflip target f A, hTflip target g A]
    rcases hIndex with h | h | h | h
    · obtain ⟨ht, htf, htg⟩ := h
      subst target
      simp [htf, htg]
    · obtain ⟨ht, hte, htg⟩ := h
      subst target
      simp [hte, htg]
    · obtain ⟨ht, hte, htf⟩ := h
      subst target
      simp [hte, htf]
    · obtain ⟨ht, htf, htg⟩ := h
      have hef : e = f := ht.symm.trans htf
      have heg : e = g := ht.symm.trans htg
      subst target
      subst f
      subst g
      simp
  change (∫ A : Cfg, obs A ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

/-- The ACTUAL four-link SU(2) plaquette real-character SQUARE has
a vanishing three-temporal-trace original spatial Haar moment,
with all repeated crossing-link indices explicitly allowed. -/
theorem p4Q2PZ11_originalPlaquetteSquare_threeTemporalTracesHaar_zero
    (p : Plaq) (e f g : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 *
      ((1 - E ((A e)⁻¹ * B e)) *
        (1 - E ((A f)⁻¹ * B f)) *
        (1 - E ((A g)⁻¹ * B g))) ∂haar) = 0 := by
  let F : C(Cfg, ℝ) :=
    ⟨(fun A : Cfg => (χ p A)^2),
      (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).pow 2⟩
  have hEven (target : Link) (A : Cfg) :
      F (Flip target A) = F A :=
    p4Q2PY7_originalPlaquetteCharSquare_centerEven H p target A
  exact p4Q2PZ11_centerEven_originalThreeTemporalTracesHaar_zero
    H F hEven e f g B

end OriginalEvenOddTripleTrace
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ11_centerEven_originalThreeTemporalTracesHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ11_originalPlaquetteSquare_threeTemporalTracesHaar_zero
