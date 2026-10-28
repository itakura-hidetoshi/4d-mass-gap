import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredGLUniformGramCriterionV5_PZ37ZX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZX2 — exact finite-family uniformity and infinite-volume boundary

At any fixed strictly-positive frozen Wilson couplings b_H, each true
physical Rayleigh R_(H,b_H)(F_t) converges at strictly positive fine to
the true centered Wilson finite-H Gram quotient (ZW3, ZX).

For ANY FINITE set of actual finite volumes S and ANY common tolerance
epsilon>0, the finite intersection of these true pointwise convergence
neighborhoods gives ONE sufficiently-small positive fine neighborhood
working for ALL H in S simultaneously.

If the ORIGINAL Gram family satisfies the exact centered lower bound
c ||V_H||² <= a_H^T G_(H,b_H) a_H for H in S (with c>0), the common
neighborhood even has R_(H,b_H)(F_t) >= c/2 for each H in S.

An arbitrary infinite collection cannot be substituted for S here.
A shared infinite-volume fine interval would require independent
uniform control of convergence; none is assumed or concluded.
The two original interacting Wilson posteriors, all links, full
pair-Haar boundary integral, and original physical Hilbert source
are unchanged, as are the Lean and mathlib pins. No new axiom,
sorry, admit, native_decide, compensating-context no-go reversal,
endpoint E/F, H1-H4 or continuum Yang–Mills mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZX2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZX2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZX2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZX2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZX2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZX2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Finite-family uniform convergence of the LITERAL original Wilson
physical Rayleigh quotients at positive fine, at fixed genuine frozen
Wilson coupling for each actual finite volume. The same fine
neighborhood works for all elements of the finite set. -/
theorem p4Q2PZ37ZX2_originalFiniteVolumes_eventually_uniformRayleighError
    (b : ℕ → ℝ) (hb : ∀ H : ℕ, 0 < b H)
    (S : Finset ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ t : Set.Ici (0 : ℝ) in
      𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)),
      ∀ H ∈ S,
        |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
            (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| < epsilon := by
  classical
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  have hSingle (H : ℕ) :
      ∀ᶠ t : Set.Ici (0 : ℝ) in 𝓝[>] t0,
        |p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) -
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
            (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)| < epsilon := by
    have hTend :=
      p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit
        H (b H) (hb H)
    have hEvent := (Metric.tendsto_nhds.mp hTend) epsilon hepsilon
    filter_upwards [hEvent] with t ht
    simpa only [Real.dist_eq] using ht
  induction S using Finset.induction_on with
  | empty =>
    exact Filter.Eventually.of_forall (by
      intro t H hH
      simp at hH)
  | @insert H S hnot ih =>
    filter_upwards [hSingle H, ih] with t htH htS
    intro K hK
    rcases Finset.mem_insert.mp hK with hKH | hKS
    · rw [hKH]
      exact htH
    · exact htS K hKS

/-- An original finite-volume Gram certificate, with true physical
source norms, turns finite-family common Rayleigh convergence into
a shared strictly-positive fine-neighborhood Rayleigh floor c/2.
The certificate is not asserted to exist uniformly for infinite H. -/
theorem p4Q2PZ37ZX2_originalFiniteVolumes_eventually_halfGramFloor
    (b : ℕ → ℝ) (hb : ∀ H : ℕ, 0 < b H)
    (S : Finset ℕ) (c : ℝ) (hc : 0 < c)
    (hGram : ∀ H ∈ S,
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) :
    ∀ᶠ t : Set.Ici (0 : ℝ) in
      𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)),
      ∀ H ∈ S,
        c / 2 ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
          H (b H) (hb H) (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  have hClose :=
    p4Q2PZ37ZX2_originalFiniteVolumes_eventually_uniformRayleighError
      b hb S (c / 2) (half_pos hc)
  filter_upwards [hClose] with t ht
  intro H hHS
  have hDen : 0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  have hLower :
      c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H) (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
    exact (le_div_iff₀ hDen).mpr (hGram H hHS)
  have hDifference := (abs_lt.mp (ht H hHS)).1
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX2_originalFiniteVolumes_eventually_uniformRayleighError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX2_originalFiniteVolumes_eventually_halfGramFloor
