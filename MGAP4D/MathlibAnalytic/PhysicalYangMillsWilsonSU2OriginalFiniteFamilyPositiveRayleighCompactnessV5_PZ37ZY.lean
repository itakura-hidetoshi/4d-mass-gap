import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteVolumeFineRayleighUniformityV5_PZ37ZX2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZY — finite-volume Wilson Rayleigh positive-family compactness

The ORIGINAL two interacting Wilson posteriors, full spatial-link sum,
pair-Haar integral, physical Gauss-law source and genuine ZW3 strict
fine-zero Rayleigh are unchanged.

For any finite set S of genuine Wilson volumes and any positive frozen
couplings b_H, positivity of EACH original centered Rayleigh value on
S gives an ACTUAL shared positive constant c_S via finite infimum.
ZX's exact original Gram equality turns that c_S into a genuine
physical-norm Gram inequality. ZX2 then supplies one common positive
fine neighborhood with an original physical Rayleigh floor c_S/2.

No uniform-in-ALL-volume c or common positive fine radius is
inferred from finite intersections. Thus this lemma identifies the
finite compactness step while preserving the infinite-family
uniformity obstruction. No surrogate posterior, new axiom,
sorry/admit/native_decide, H1-H4, endpoint E/F, or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZY_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Finite positivity of the ACTUAL physical centered Wilson GL
Rayleigh values produces one fixed positive lower witness for the
whole finite family. The witness may depend on the finite set. -/
theorem p4Q2PZ37ZY_finiteCenteredRayleigh_exists_positive_floor
    (b : ℕ → ℝ) (hb : ∀ H : ℕ, 0 < b H)
    (S : Finset ℕ)
    (hPositive : ∀ H ∈ S,
      0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ H ∈ S,
        c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
          H (b H) (hb H)
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro H hH
      simp at hH
  | @insert H S hnot ih =>
      have hPositiveS : ∀ K ∈ S,
          0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
            K (b K) (hb K)
            (p4Q2PZ37ZW_originalCenteredPhysicalDirection K) := by
        intro K hK
        exact hPositive K (Finset.mem_insert_of_mem hK)
      obtain ⟨c, hc, hcS⟩ := ih hPositiveS
      let v : ℝ := p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
      have hv : 0 < v :=
        hPositive H (Finset.mem_insert_self H S)
      refine ⟨min c v, lt_min hc hv, ?_⟩
      intro K hK
      rcases Finset.mem_insert.mp hK with hKH | hKS
      · subst K
        exact min_le_right c v
      · exact (min_le_left c v).trans (hcS K hKS)

/-- A finite collection of genuine pointwise positive centered
Wilson physical Rayleigh limits automatically admits a common
strict positive-fine Rayleigh neighborhood, with a positive but
finite-family-dependent floor. This is not an infinite-volume
coercivity theorem. -/
theorem p4Q2PZ37ZY_finiteOriginalVolumes_exists_commonPositiveFineFloor
    (b : ℕ → ℝ) (hb : ∀ H : ℕ, 0 < b H)
    (S : Finset ℕ)
    (hPositive : ∀ H ∈ S,
      0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ t : Set.Ici (0 : ℝ) in
        𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)),
        ∀ H ∈ S,
          c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
            H (b H) (hb H)
            (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  obtain ⟨d, hd, hFloor⟩ :=
    p4Q2PZ37ZY_finiteCenteredRayleigh_exists_positive_floor
      b hb S hPositive
  have hGram : ∀ H ∈ S,
      d * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H) := by
    intro H hHS
    have hDen : 0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
      pow_pos (norm_pos_iff.mpr
        (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
    have hH := hFloor H hHS
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
      at hH
    exact (le_div_iff₀ hDen).mp hH
  refine ⟨d / 2, half_pos hd, ?_⟩
  exact p4Q2PZ37ZX2_originalFiniteVolumes_eventually_halfGramFloor
    b hb S d hd hGram

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZY_finiteCenteredRayleigh_exists_positive_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZY_finiteOriginalVolumes_exists_commonPositiveFineFloor
