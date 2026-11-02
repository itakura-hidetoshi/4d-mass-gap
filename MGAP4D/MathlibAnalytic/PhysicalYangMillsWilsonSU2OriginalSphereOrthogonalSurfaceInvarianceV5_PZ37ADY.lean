import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereAmbientOrthogonalV5_PZ37ADX
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADY — Mathlib sphere surface invariance for ORIGINAL SU(2)

ADX identifies the authentic original SU(2) left action on S³ with an
ambient four-dimensional real linear isometry equivalence. Here the
fixed Mathlib volume-preservation theorem and its polar-sector formula
are used to prove invariance of the INDEPENDENT toSphere surface measure.
Normalization then inherits the same invariance, and the existing ADU
Haar-probability uniqueness bridge identifies the two measures.

This is an append-only measure-theoretic descent, not a replacement of
the original interacting Wilson SU(2), boundary pair-Haar, Gauss-law
source, FF receiver, transfer operator, or physical posterior. No
H-uniform coercivity or continuum mass gap is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators Pointwise

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "act" => p4Q2PZ37ADU_originalLeftActionOnSphere
local notation "surf" => Measure.toSphere (volume : Measure E4)
local notation "L" => p4Q2PZ37ADX_originalAmbientLinearIsometry

/-- The literal radial region used by fixed-mathlib toSphere_apply'. -/
def p4Q2PZ37ADY_radialSector (s : Set S3) : Set E4 :=
  Set.Ioo (0 : ℝ) 1 • ((fun u : S3 => (u : E4)) '' s)

/-- A radial-sector preimage commutes exactly with the ORIGINAL SU(2)
sphere action. The key input is ADX's ambient orthogonal extension;
no measurable-set assumption or surrogate sphere group is needed. -/
theorem p4Q2PZ37ADY_radialSector_preimage (g : G) (s : Set S3) :
    (L g) ⁻¹' p4Q2PZ37ADY_radialSector s =
      p4Q2PZ37ADY_radialSector ((act g) ⁻¹' s) := by
  let e : E4 ≃ₗᵢ[ℝ] E4 := L g
  have hAction (u : S3) : e (u : E4) = (act g u : E4) :=
    p4Q2PZ37ADX_originalAmbient_eq_originalSphereAction g u
  ext x
  constructor
  · intro hx
    change e x ∈
      Set.Ioo (0 : ℝ) 1 • ((fun u : S3 => (u : E4)) '' s) at hx
    rcases hx with ⟨r, hr, y, hy, hEq⟩
    rcases hy with ⟨u, hu, rfl⟩
    let v : S3 := act g⁻¹ u
    have hv : act g v = u := by
      dsimp [v]
      exact p4Q2PZ37ADV_originalLeftAction_inv_right g u
    have hEv : e (v : E4) = (u : E4) := by
      rw [hAction v, hv]
    change x ∈ p4Q2PZ37ADY_radialSector ((act g) ⁻¹' s)
    refine ⟨r, hr, (v : E4), ⟨v, ?_, rfl⟩, ?_⟩
    · change act g v ∈ s
      rw [hv]
      exact hu
    · apply e.injective
      calc
        e (r • (v : E4)) = r • e (v : E4) := e.map_smul r (v : E4)
        _ = r • (u : E4) := by rw [hEv]
        _ = e x := hEq
  · intro hx
    change x ∈
      Set.Ioo (0 : ℝ) 1 •
        ((fun u : S3 => (u : E4)) '' ((act g) ⁻¹' s)) at hx
    rcases hx with ⟨r, hr, y, hy, hEq⟩
    rcases hy with ⟨u, hu, rfl⟩
    change e x ∈ p4Q2PZ37ADY_radialSector s
    refine ⟨r, hr, (act g u : E4), ⟨act g u, hu, rfl⟩, ?_⟩
    calc
      r • (act g u : E4) = r • e (u : E4) := by rw [hAction u]
      _ = e (r • (u : E4)) := (e.map_smul r (u : E4)).symm
      _ = e x := by rw [hEq]

/-- Unnormalized Mathlib S³ surface measure is preserved by each
ACTUAL original SU(2) left action. This uses the full radial-sector
identity and real-four-dimensional Lebesgue volume preservation. -/
theorem p4Q2PZ37ADY_originalLeftAction_preservesSurface (g : G) :
    Measure.map (act g) surf = surf := by
  let e : E4 ≃ₗᵢ[ℝ] E4 := L g
  have hm : MeasurePreserving e (volume : Measure E4) (volume : Measure E4) :=
    LinearIsometryEquiv.measurePreserving e
  have ha : Measurable (act g) :=
    (p4Q2PZ37ADU_originalLeftAction_continuous g).measurable
  ext s hs
  have hSector :
      (volume : Measure E4)
        (p4Q2PZ37ADY_radialSector ((act g) ⁻¹' s)) =
      (volume : Measure E4) (p4Q2PZ37ADY_radialSector s) := by
    rw [← p4Q2PZ37ADY_radialSector_preimage g s]
    have hMap := e.toMeasurableEquiv.map_apply
      (μ := (volume : Measure E4)) (p4Q2PZ37ADY_radialSector s)
    change (Measure.map e (volume : Measure E4))
      (p4Q2PZ37ADY_radialSector s) =
        (volume : Measure E4) (e ⁻¹' p4Q2PZ37ADY_radialSector s) at hMap
    rw [hm.map_eq] at hMap
    exact hMap.symm
  rw [Measure.map_apply ha hs]
  rw [Measure.toSphere_apply' (volume : Measure E4) (ha hs),
      Measure.toSphere_apply' (volume : Measure E4) hs]
  change (Module.finrank ℝ E4 : ℕ) *
      (volume : Measure E4)
        (p4Q2PZ37ADY_radialSector ((act g) ⁻¹' s)) =
    (Module.finrank ℝ E4 : ℕ) *
      (volume : Measure E4) (p4Q2PZ37ADY_radialSector s)
  rw [hSector]

local instance p4Q2PZ37ADY_nonemptySphere : Nonempty S3 :=
  ⟨p4Q2PZ37ADR_originalSU2ToSphere (1 : G)⟩

/-- The true probability normalization of Mathlib surface measure is
likewise invariant; a nonzero total surface mass is proved from
Mathlib's positive-dimensional toSphere theorem. -/
theorem p4Q2PZ37ADY_originalLeftAction_preservesNormalizedSurface
    (g : G) :
    Measure.map (act g)
      (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) =
        (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) := by
  let μ : FiniteMeasure S3 := ⟨surf, inferInstance⟩
  have hμ : μ ≠ 0 := by
    intro h
    have hh : (μ : Measure S3) = 0 :=
      congrArg (fun m : FiniteMeasure S3 => (m : Measure S3)) h
    exact (Measure.toSphere_ne_zero (volume : Measure E4))
      (by simpa [μ] using hh)
  have hRaw : Measure.map (act g) (μ : Measure S3) = (μ : Measure S3) := by
    change Measure.map (act g) surf = surf
    exact p4Q2PZ37ADY_originalLeftAction_preservesSurface g
  change Measure.map (act g) (μ.normalize : Measure S3) =
    (μ.normalize : Measure S3)
  rw [μ.toMeasure_normalize_eq_of_nonzero hμ,
    Measure.map_smul _
      (p4Q2PZ37ADU_originalLeftAction_continuous g).measurable.aemeasurable,
    hRaw]

/-- Unconditional identification: ORIGINAL compact SU(2) Haar,
transported by the ORIGINAL matrix/S³ homeomorphism, is precisely
the independent normalized fixed-mathlib S³ surface probability. -/
theorem p4Q2PZ37ADY_originalHaarSphere_eq_normalizedSurface :
    p4Q2PZ37ADU_originalHaarOnSphere =
      (p4Q2PZ37ADU_normalizedMathlibSphereSurface : Measure S3) :=
  p4Q2PZ37ADU_originalHaar_eq_mathlibSphere_of_surfaceInvariant
    p4Q2PZ37ADY_originalLeftAction_preservesNormalizedSurface

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_radialSector_preimage
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_originalLeftAction_preservesSurface
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_originalLeftAction_preservesNormalizedSurface
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADY_originalHaarSphere_eq_normalizedSurface
