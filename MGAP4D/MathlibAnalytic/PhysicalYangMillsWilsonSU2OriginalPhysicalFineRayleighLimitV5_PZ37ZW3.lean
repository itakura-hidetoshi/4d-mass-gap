import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLQuadraticContinuityV5_PZ37ZW2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZW3 — TRUE original Wilson physical Rayleigh fine-zero limit

On the same original finite Wilson two-interacting-posterior Gauss-law
Hilbert source, lift ZV2's strong Wilson tangent (not a redefined
surrogate) to the genuine continuous-Haar-represented physical subspace.
Use ZW2's exact full-link GL quadratic and norm continuity there.

For positive fine t, ZV2 identifies that tangent with F_t/t. Exact
quadratic scaling cancels t² in the TRUE physical Rayleigh quotient.
Its strictly right-sided fine-zero limit is the Rayleigh of the
centered genuine Wilson action V_H, which ZW proves strictly positive.

The normalized Rayleigh of F_0 itself is not assigned a positive
value: F_0=0, so fine=0 remains a punctured endpoint. The result
is fixed finite H and fixed positive frozen b; no H-uniform bound,
endpoint E/F, H1-H4 or continuum Yang–Mills mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZW3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZW3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZW3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZW3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZW3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZW3_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The strict original centered physical direction has an actual
continuous Wilson-Haar representative (the original ZN two-mode
Wilson combination), not merely an unspecified L2 version. -/
theorem p4Q2PZ37ZW3_originalCenteredDirection_has_continuousRepresentative
    (H : ℕ) :
    p4Q2PZ37ZW_originalCenteredPhysicalDirection H ∈
      p4Q2PZ37ZW2_originalContinuousPhysicalSources H := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let a := p4Q2PZ37ZW_originalCenteredCoefficients H
  change ∃ ψ : C(Cfg, ℝ),
    ((p4Q2PZ37ZW_originalCenteredPhysicalDirection H :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = ContinuousMap.toLp 2 haar ℝ ψ
  rw [p4Q2PZ37ZW_originalCenteredDirection_eq_static]
  exact ⟨a 0 • (1 : C(Cfg, ℝ)) +
      a 1 • p4Q2JI_actualSpatialWilsonContinuous H,
    p4Q2PZ37ZN_originalStaticPhysicalSource_coe_eq_toLp H a⟩

/-- Every ZV2 fine-tangent source, including its distinguished fine=0
value, is represented by the original continuous Haar row and the
exact normalizing scalar. This keeps the genuine source carrier. -/
theorem p4Q2PZ37ZW3_originalFullPhysicalTangent_has_continuousRepresentative
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t ∈
      p4Q2PZ37ZW2_originalContinuousPhysicalSources H := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let a : ℝ := p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H t
  let r : ℝ := (t : ℝ)⁻¹
  let Err : Phys := p4Q2PZ37ZT_originalPhysicalErrorDivFine H t
  let ψErr : C(Cfg, ℝ) :=
    p4Q2JF_originalWilsonHaarRowContinuous H (t : ℝ) -
      (1 : C(Cfg, ℝ)) -
      (t : ℝ) • p4Q2JE_originalWilsonHaarZeroDerivativeProfile H
  have hErr : (Err : Lp ℝ 2 haar) = L (r • ψErr) := by
    change r •
      ((p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t : Phys) : Lp ℝ 2 haar) =
      L (r • ψErr)
    rw [p4Q2PZ37ZQ_originalPhysicalRawTaylorError_coe_eq_toLp H t, map_smul]
  change ∃ ψ : C(Cfg, ℝ),
    ((p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t : Phys) :
      Lp ℝ 2 haar) = L ψ
  refine ⟨a • (1 : C(Cfg, ℝ)) +
      (s / 2) • p4Q2JI_actualSpatialWilsonContinuous H -
        s • (r • ψErr), ?_⟩
  change
    (((a • U + ((s / 2) • W - s • Err) : Phys) : Lp ℝ 2 haar) =
      L (a • (1 : C(Cfg, ℝ)) +
        (s / 2) • p4Q2JI_actualSpatialWilsonContinuous H - s • (r • ψErr))
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
    hErr, map_add, map_sub, map_smul]

/-- The true centered source, with the inherited original physical
Hilbert norm. -/
noncomputable def p4Q2PZ37ZW3_originalCenteredPhysicalLift
    (H : ℕ) : p4Q2PZ37ZW2_originalContinuousPhysicalSources H :=
  ⟨p4Q2PZ37ZW_originalCenteredPhysicalDirection H,
    p4Q2PZ37ZW3_originalCenteredDirection_has_continuousRepresentative H⟩

/-- The original ZV2 physical tangent, lifted to the same Hilbert-norm
submodule solely by its actual continuous Haar representative. -/
noncomputable def p4Q2PZ37ZW3_originalFullPhysicalTangentLift
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    p4Q2PZ37ZW2_originalContinuousPhysicalSources H :=
  ⟨p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t,
    p4Q2PZ37ZW3_originalFullPhysicalTangent_has_continuousRepresentative H t⟩

/-- ZV's actual physical-Hilbert strong convergence is also genuine
Hilbert norm convergence in the represented-source subspace; no
completion, surrogate source, or topology weakening occurs. -/
theorem p4Q2PZ37ZW3_originalFullPhysicalTangentLift_tendsto
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZW3_originalFullPhysicalTangentLift H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2PZ37ZW3_originalCenteredPhysicalLift H)) := by
  have h := p4Q2PZ37ZW_originalFullPhysicalTangent_tendsto_centered H
  rw [Metric.tendsto_nhds] at h ⊢
  intro eps heps
  filter_upwards [h eps heps] with t ht
  simpa only [Subtype.dist_eq] using ht

/-- Exact degree-two GL homogeneity on original physical sources with
a continuous Haar representative, derived from the LITERAL two-posterior
full-link Haar bilinear form, not a new quadratic normalization axiom. -/
theorem p4Q2PZ37ZW3_originalGLMass_smul
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c : ℝ)
    (f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le
      ((c • f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) =
      c^2 *
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let B := p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear H b hb
  calc
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
      ((c • f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) =
        B (c • f) (c • f) :=
      (p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL
        H b hb (c • f)).symm
    _ = c^2 * B f f := by
      simp only [map_smul, smul_eq_mul]
      ring
    _ = c^2 *
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
      rw [p4Q2PZ37ZW2_originalFullLinkGLPhysicalBilinear_self_eq_originalGL]

/-- A nonzero physical fine scalar cancels EXACTLY from the source-
normalized original GL Rayleigh ratio; this lemma applies even if the
represented source itself is zero. -/
theorem p4Q2PZ37ZW3_originalGLRayleigh_smul
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c : ℝ) (hc : c ≠ 0)
    (f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le
      ((c • f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
      ‖(c • f : p4Q2PZ37ZW2_originalContinuousPhysicalSources H)‖^2 =
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
      ‖f‖^2 := by
  rw [p4Q2PZ37ZW3_originalGLMass_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

/-- The numerator is continuous along the actual lifted normalized
physical tangent in the SAME full-link GL mass. -/
theorem p4Q2PZ37ZW3_originalTangentGLMass_tendsto_center
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : Set.Ici (0 : ℝ) =>
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        ((p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        ((p4Q2PZ37ZW3_originalCenteredPhysicalLift H :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))) := by
  have hContAt :=
    (p4Q2PZ37ZW2_originalFullLinkGLPhysicalMass_continuous H b hb).continuousAt
      (x := p4Q2PZ37ZW3_originalCenteredPhysicalLift H)
  exact hContAt.comp (p4Q2PZ37ZW3_originalFullPhysicalTangentLift_tendsto H)

/-- ORIGINAL unnormalized Wilson cancellation has the exact positive-
fine physical-Hilbert identity F_t=t*(ZV true tangent). -/
theorem p4Q2PZ37ZW3_originalPhysicalCancellation_eq_fine_smulLift
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    p4Q2PZ37ZE_originalPhysicalCancellation H t =
      (t : ℝ) •
        (p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) := by
  change p4Q2PZ37ZE_originalPhysicalCancellation H t =
    (t : ℝ) • p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t
  rw [← p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_positive H t ht,
    smul_smul]
  simp [ne_of_gt ht]

/-- Original full-link GL mass divided by fine² converges from
STRICTLY POSITIVE fine to the genuine centered Wilson physical GL mass. -/
theorem p4Q2PZ37ZW3_originalPhysicalGLMass_div_fine_sq_tendsto
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : Set.Ici (0 : ℝ) =>
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
      (t : ℝ)^2)
      (𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  have hPos : ∀ᶠ t : Set.Ici (0 : ℝ) in 𝓝[>] t0, 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hBase := p4Q2PZ37ZW3_originalTangentGLMass_tendsto_center H b hb
  have hBase' : Tendsto (fun t : Set.Ici (0 : ℝ) =>
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        ((p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (𝓝[>] t0)
      (𝓝 (p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))) := by
    exact hBase.mono_left nhdsWithin_le_nhds
  have hEq (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
      (t : ℝ)^2 =
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        ((p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
    rw [p4Q2PZ37ZW3_originalPhysicalCancellation_eq_fine_smulLift H t ht]
    have hScale := p4Q2PZ37ZW3_originalGLMass_smul H b hb
      (t : ℝ) (p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t)
    change
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
        (((t : ℝ) • p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
        (t : ℝ)^2 = _
    rw [hScale]
    field_simp [ne_of_gt ht]
  exact hBase'.congr' (hPos.mono fun t ht => (hEq t ht).symm)

/-- The ACTUAL physical GL Rayleigh of F_t is literally that of the
continuously represented ZV tangent at each strictly positive fine. -/
theorem p4Q2PZ37ZW3_originalPositiveFine_Rayleigh_eq_tangent
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZE_originalPhysicalCancellation H t) =
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
      ((p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
        p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
    ‖p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t‖^2 := by
  unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
  rw [p4Q2PZ37ZW3_originalPhysicalCancellation_eq_fine_smulLift H t ht]
  change
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
      (((t : ℝ) • p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
          p4Q2PZ37ZW2_originalContinuousPhysicalSources H) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) /
      ‖((t : ℝ) • p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t :
        p4Q2PZ37ZW2_originalContinuousPhysicalSources H)‖^2 =
    _
  exact p4Q2PZ37ZW3_originalGLRayleigh_smul H b hb
    (t : ℝ) (ne_of_gt ht)
    (p4Q2PZ37ZW3_originalFullPhysicalTangentLift H t)

/-- The final original full-link GL physical Rayleigh has its EXACT
strict positive-fine zero limit, the positive Rayleigh of the ZV
centered genuine Wilson physical source. No Rayleigh(0) convention. -/
theorem p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : Set.Ici (0 : ℝ) =>
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t))
      (𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H))) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let f := p4Q2PZ37ZW3_originalFullPhysicalTangentLift H
  let V := p4Q2PZ37ZW3_originalCenteredPhysicalLift H
  let Q := fun u : p4Q2PZ37ZW2_originalContinuousPhysicalSources H =>
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
      (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hMass : Tendsto (fun t : Set.Ici (0 : ℝ) => Q (f t))
      (𝓝 t0) (𝓝 (Q V)) :=
    p4Q2PZ37ZW3_originalTangentGLMass_tendsto_center H b hb
  have hT := p4Q2PZ37ZW3_originalFullPhysicalTangentLift_tendsto H
  have hNorm : Tendsto (fun t : Set.Ici (0 : ℝ) => ‖f t‖^2)
      (𝓝 t0) (𝓝 (‖V‖^2)) := hT.norm.pow 2
  have hV : V ≠ 0 := by
    intro hv
    apply p4Q2PZ37ZW_originalCenteredDirection_ne_zero H
    have h := congrArg (fun x :
      p4Q2PZ37ZW2_originalContinuousPhysicalSources H =>
      (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) hv
    simpa only [p4Q2PZ37ZW3_originalCenteredPhysicalLift, Submodule.coe_zero] using h
  have hDen : ‖V‖^2 ≠ 0 :=
    ne_of_gt (pow_pos (norm_pos_iff.mpr hV) 2)
  have hRatio : Tendsto (fun t : Set.Ici (0 : ℝ) => Q (f t) / ‖f t‖^2)
      (𝓝 t0) (𝓝 (Q V / ‖V‖^2)) :=
    hMass.div hNorm hDen
  have hPos : ∀ᶠ t : Set.Ici (0 : ℝ) in 𝓝[>] t0, 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hEq : (fun t : Set.Ici (0 : ℝ) =>
    p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)) =ᶠ[𝓝[>] t0]
      (fun t : Set.Ici (0 : ℝ) => Q (f t) / ‖f t‖^2) := by
    filter_upwards [hPos] with t ht
    exact p4Q2PZ37ZW3_originalPositiveFine_Rayleigh_eq_tangent H b hb t ht
  have hLimit : Q V / ‖V‖^2 =
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := rfl
  rw [← hLimit]
  exact (hRatio.mono_left nhdsWithin_le_nhds).congr' hEq.symm

/-- The genuine original Wilson fine-zero physical Rayleigh limit
EXISTS, is IDENTIFIED, and is STRICTLY POSITIVE for every fixed
finite H and positive frozen b, using ZN on true Wilson contexts. -/
theorem p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) ∧
    Tendsto (fun t : Set.Ici (0 : ℝ) =>
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZE_originalPhysicalCancellation H t))
      (𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H))) := by
  exact ⟨p4Q2PZ37ZW_originalCenteredDirection_Rayleigh_pos
      H b hb e e' left₀ right₀,
    p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit H b hb⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalFullPhysicalTangent_has_continuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalFullPhysicalTangentLift_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalGLMass_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalPhysicalGLMass_div_fine_sq_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit_pos
