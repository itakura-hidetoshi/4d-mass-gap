import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2Original24SignObstructionV5_PZ37AHF
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHG — explicit original rational stereographic mesh

AHF rules out improving the literal original24 sign checker by orders or
mass precision alone. AHG specifies a NEW certificate grid on the SAME
original SU(2), not a new physical model: two antipodal AGR charts with
parameters k/N-1, k in {0,...,2N}, in each of three coordinates.

An exact stereographic chord-square identity and natural-floor rounding
prove a cover of the original SU(2) by the 2*(2N+1)^3 indexed rational
centers at true chordal radius 4/N. No compactness-selected subcover or
rational-density choice specifies this center family. Repeated centers
are allowed; the count is a count of labels, not distinct group elements.

Original AGH first-center Borel product cells and original AGU precision
Types receive this cover. Their spatial radius is 4*p_H/N. At N=128 it
is p_H/32<p_H/24, below AHF's necessary uniform-radius threshold.

Finite reindexing and AGQ TRUE Haar mass enclosure selection still use
classical constructions. This does NOT numerically evaluate those masses
or the enormous spatial product table, and does NOT certify an actual
nonzero signed transfer, two-sign shell, uniform coercivity or mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "V" => p4Q2PZ37AGS_realStereographicVector

/-- Exact chord-square identity for the SAME AGR/AGS stereographic map. -/
theorem p4Q2PZ37AHG_stereographic_dist_sq (u v : Fin 3 → ℝ) :
    dist (V u) (V v) ^ 2 =
      4 * (∑ j : Fin 3, (u j - v j)^2) /
        ((1 + ∑ j : Fin 3, (u j)^2) * (1 + ∑ j : Fin 3, (v j)^2)) := by
  have hu : 0 < 1 + ((u 0)^2 + (u 1)^2 + (u 2)^2) := by positivity
  have hv : 0 < 1 + ((v 0)^2 + (v 1)^2 + (v 2)^2) := by positivity
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin 4,
    (p4Q2PZ37AGS_realSphereCoordinates u j - p4Q2PZ37AGS_realSphereCoordinates v j)^2) = _
  simp only [Fin.sum_univ_four, Fin.sum_univ_three]
  change
    ((1 - ((u 0)^2 + (u 1)^2 + (u 2)^2)) / (1 + ((u 0)^2 + (u 1)^2 + (u 2)^2)) -
      (1 - ((v 0)^2 + (v 1)^2 + (v 2)^2)) / (1 + ((v 0)^2 + (v 1)^2 + (v 2)^2)))^2 +
    (2 * u 0 / (1 + ((u 0)^2 + (u 1)^2 + (u 2)^2)) -
      2 * v 0 / (1 + ((v 0)^2 + (v 1)^2 + (v 2)^2)))^2 +
    (2 * u 1 / (1 + ((u 0)^2 + (u 1)^2 + (u 2)^2)) -
      2 * v 1 / (1 + ((v 0)^2 + (v 1)^2 + (v 2)^2)))^2 +
    (2 * u 2 / (1 + ((u 0)^2 + (u 1)^2 + (u 2)^2)) -
      2 * v 2 / (1 + ((v 0)^2 + (v 1)^2 + (v 2)^2)))^2 =
      4 * ((u 0 - v 0)^2 + (u 1 - v 1)^2 + (u 2 - v 2)^2) /
        ((1 + ((u 0)^2 + (u 1)^2 + (u 2)^2)) *
          (1 + ((v 0)^2 + (v 1)^2 + (v 2)^2)))
  field_simp [ne_of_gt hu, ne_of_gt hv]
  <;> ring

/-- A strict 4*e chord bound from coordinatewise errors <=e.
The slack 12*e^2<16*e^2 makes the cover OPEN even at mesh endpoints. -/
theorem p4Q2PZ37AHG_stereographic_dist_lt
    (u v : Fin 3 → ℝ) (e : ℝ) (he : 0 < e)
    (hClose : ∀ j, |u j - v j| ≤ e) : dist (V u) (V v) < 4 * e := by
  let D := (1 + ∑ j : Fin 3, (u j)^2) * (1 + ∑ j : Fin 3, (v j)^2)
  have hu : 0 ≤ ∑ j : Fin 3, (u j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : 0 ≤ ∑ j : Fin 3, (v j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith only [hu, hv, mul_nonneg hu hv]
  have hDne : D ≠ 0 := by linarith only [hD]
  have hIdentity : dist (V u) (V v)^2 * D = 4 * (∑ j : Fin 3, (u j - v j)^2) :=
    (eq_div_iff hDne).mp (p4Q2PZ37AHG_stereographic_dist_sq u v)
  have hEach (j : Fin 3) : (u j - v j)^2 ≤ e^2 := by
    obtain ⟨hl, hh⟩ := abs_le.mp (hClose j)
    have hp := mul_nonneg (sub_nonneg.mpr hh)
      (show 0 ≤ e + (u j - v j) by linarith only [hl])
    nlinarith only [hp]
  have hSum : (∑ j : Fin 3, (u j - v j)^2) ≤ 3 * e^2 := by
    calc
      (∑ j : Fin 3, (u j - v j)^2) ≤ ∑ _j : Fin 3, e^2 :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = 3 * e^2 := by simp
  have hMul := mul_le_mul_of_nonneg_left hD (sq_nonneg (dist (V u) (V v)))
  have hSq : dist (V u) (V v)^2 ≤ 12 * e^2 := by
    nlinarith only [hMul, hIdentity, hSum]
  nlinarith only [hSq, sq_pos_of_pos he, dist_nonneg (x := V u) (y := V v), he]

/-- A nonnegative first coordinate gives chart parameters in [-1,1]^3.
This is a bounded chart of the genuine sphere, not a density argument. -/
theorem p4Q2PZ37AHG_bounded_hemisphere_chart
    (x : S3) (ha : 0 ≤ (x : E4) 0) :
    ∃ u : Fin 3 → ℝ, (∀ j, |u j| ≤ 1) ∧ V u = (x : E4) := by
  have hn : ‖(x : E4)‖ = 1 := by
    have hx := x.property
    change dist (x : E4) (0 : E4) = 1 at hx
    simpa only [dist_zero_right] using hx
  have hsq : (∑ j : Fin 4, ((x : E4) j)^2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn]
    norm_num
  have hCoord (j : Fin 4) : |(x : E4) j| ≤ 1 := by
    have hj : ((x : E4) j)^2 ≤ ∑ k : Fin 4, ((x : E4) k)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ((x : E4) k)) (Finset.mem_univ j)
    rw [hsq] at hj
    apply abs_le.mpr
    constructor
    · nlinarith only [hj, sq_nonneg ((x : E4) j + 1)]
    · nlinarith only [hj, sq_nonneg ((x : E4) j - 1)]
  have hd : 0 < 1 + (x : E4) 0 := by linarith only [ha]
  have hParam (j : Fin 4) : |(x : E4) j / (1 + (x : E4) 0)| ≤ 1 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    linarith only [hCoord j, ha]
  let u : Fin 3 → ℝ := ![(x : E4) 1 / (1 + (x : E4) 0),
    (x : E4) 2 / (1 + (x : E4) 0), (x : E4) 3 / (1 + (x : E4) 0)]
  refine ⟨u, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hParam 1
    · exact hParam 2
    · exact hParam 3
  · have hAlg := p4Q2PZ37AGS_chartAlgebra
      ((x : E4) 0) ((x : E4) 1) ((x : E4) 2) ((x : E4) 3)
      (by simpa only [Fin.sum_univ_four] using hsq) (ne_of_gt hd)
    calc
      V u = (WithLp.toLp 2 (![(x : E4) 0, (x : E4) 1,
        (x : E4) 2, (x : E4) 3] : Fin 4 → ℝ) : E4) := hAlg
      _ = (x : E4) := by ext j; fin_cases j <;> rfl

/-- Integer mesh rounding includes BOTH endpoints of [-1,1]. -/
theorem p4Q2PZ37AHG_scalar_mesh (N : ℕ) (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ 1) :
    ∃ i : Fin (2 * N + 1), |x - ((i.val : ℝ) / (N : ℝ) - 1)| < 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  let z : ℝ := (N : ℝ) * (x + 1)
  have hz : 0 ≤ z := mul_nonneg hNr.le (by linarith only [hl])
  have hzHi : z ≤ ((2 * N : ℕ) : ℝ) := by
    dsimp [z]
    push_cast
    nlinarith only [hu, hNr]
  have hk : Nat.floor z ≤ 2 * N := Nat.floor_le_of_le hzHi
  let i : Fin (2 * N + 1) := ⟨Nat.floor z, Nat.lt_succ_of_le hk⟩
  refine ⟨i, ?_⟩
  have hLo : ((i.val : ℝ)) ≤ (N : ℝ) * (x + 1) := Nat.floor_le hz
  have hHi : (N : ℝ) * (x + 1) < (i.val : ℝ) + 1 := Nat.lt_floor_add_one z
  have hDiv : (i.val : ℝ) / (N : ℝ) * (N : ℝ) = (i.val : ℝ) :=
    div_mul_cancel₀ _ hNr.ne'
  have hApprox : (i.val : ℝ) / (N : ℝ) ≤ x + 1 :=
    (div_le_iff₀ hNr).2 (by nlinarith only [hLo])
  have hNonneg : 0 ≤ x - ((i.val : ℝ) / (N : ℝ) - 1) := by
    linarith only [hApprox]
  rw [abs_of_nonneg hNonneg]
  apply (lt_div_iff₀ hNr).2
  nlinarith only [hHi, hDiv]

/-- Explicit finite lattice labels. No centers are chosen by compactness. -/
abbrev p4Q2PZ37AHG_meshIndex (N : ℕ) := Bool × (Fin 3 → Fin (2 * N + 1))

def p4Q2PZ37AHG_meshParameters (N : ℕ) (a : Fin 3 → Fin (2 * N + 1)) : Fin 3 → ℚ :=
  fun j => ((a j).val : ℚ) / (N : ℚ) - 1

def p4Q2PZ37AHG_originalMeshCenter (N : ℕ) (i : p4Q2PZ37AHG_meshIndex N) : G :=
  p4Q2PZ37AGS_originalSignedCenter i.1 (p4Q2PZ37AHG_meshParameters N i.2)

theorem p4Q2PZ37AHG_meshIndex_card (N : ℕ) :
    Fintype.card (p4Q2PZ37AHG_meshIndex N) = 2 * (2 * N + 1)^3 := by
  simp [p4Q2PZ37AHG_meshIndex]

/-- The mesh cardinal is a label count; antipodal chart images may overlap. -/
theorem p4Q2PZ37AHG_mesh128_card :
    Fintype.card (p4Q2PZ37AHG_meshIndex 128) = 33949186 := by
  rw [p4Q2PZ37AHG_meshIndex_card]
  norm_num

/-- Exact original AGL rational-coordinate evidence for EVERY label. -/
def p4Q2PZ37AHG_originalMeshCenter_rational
    (N : ℕ) (i : p4Q2PZ37AHG_meshIndex N) :
    p4Q2PZ37AGL_rationalCoordinates (p4Q2PZ37AHG_originalMeshCenter N i) :=
  p4Q2PZ37AGT_originalSignedCenter_rational i.1 (p4Q2PZ37AHG_meshParameters N i.2)

/-- Deterministic integer rounding approximates the entire hemisphere. -/
theorem p4Q2PZ37AHG_hemisphere_mesh_cover
    (N : ℕ) (hN : 0 < N) (x : S3) (ha : 0 ≤ (x : E4) 0) :
    ∃ a : Fin 3 → Fin (2 * N + 1),
      dist x (p4Q2PZ37AGR_rationalSphere (p4Q2PZ37AHG_meshParameters N a)) < 4 / (N : ℝ) := by
  obtain ⟨u, hu, hEq⟩ := p4Q2PZ37AHG_bounded_hemisphere_chart x ha
  choose a ha using (fun j : Fin 3 => p4Q2PZ37AHG_scalar_mesh N hN (u j) (hu j))
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hClose (j : Fin 3) : |u j - (p4Q2PZ37AHG_meshParameters N a j : ℝ)| ≤ 1 / (N : ℝ) := by
    simpa [p4Q2PZ37AHG_meshParameters] using (ha j).le
  have hD := p4Q2PZ37AHG_stereographic_dist_lt u
    (fun j => (p4Q2PZ37AHG_meshParameters N a j : ℝ))
    (1 / (N : ℝ)) (div_pos (by norm_num) hNr) hClose
  rw [p4Q2PZ37AGS_rationalVector_exact, hEq] at hD
  refine ⟨a, ?_⟩
  change dist (x : E4) (p4Q2PZ37AGR_rationalSphere (p4Q2PZ37AHG_meshParameters N a) : E4) < _
  calc
    dist (x : E4) (p4Q2PZ37AGR_rationalSphere (p4Q2PZ37AHG_meshParameters N a) : E4) <
      4 * (1 / (N : ℝ)) := hD
    _ = 4 / (N : ℝ) := by ring

/-- Two specified antipodal meshes cover the WHOLE original sphere. -/
theorem p4Q2PZ37AHG_sphere_mesh_cover (N : ℕ) (hN : 0 < N) (x : S3) :
    ∃ i : p4Q2PZ37AHG_meshIndex N,
      dist x (p4Q2PZ37AGS_signedRationalSphere i.1
        (p4Q2PZ37AHG_meshParameters N i.2)) < 4 / (N : ℝ) := by
  by_cases h0 : 0 ≤ (x : E4) 0
  · obtain ⟨a, ha⟩ := p4Q2PZ37AHG_hemisphere_mesh_cover N hN x h0
    refine ⟨(false, a), ?_⟩
    simpa [p4Q2PZ37AGS_signedRationalSphere] using ha
  · have hAnti : 0 ≤ (p4Q2PZ37AGS_antipode x : E4) 0 := by
      rw [p4Q2PZ37AGS_antipode_apply]
      linarith only [lt_of_not_ge h0]
    obtain ⟨a, ha⟩ := p4Q2PZ37AHG_hemisphere_mesh_cover N hN
      (p4Q2PZ37AGS_antipode x) hAnti
    refine ⟨(true, a), ?_⟩
    have hDist : dist x (p4Q2PZ37AGS_antipode
        (p4Q2PZ37AGR_rationalSphere (p4Q2PZ37AHG_meshParameters N a))) =
      dist (p4Q2PZ37AGS_antipode x)
        (p4Q2PZ37AGR_rationalSphere (p4Q2PZ37AHG_meshParameters N a)) := by
      calc
        dist x _ = dist (p4Q2PZ37AGS_antipode (p4Q2PZ37AGS_antipode x)) _ := by
          rw [p4Q2PZ37AGS_antipode_involutive]
        _ = _ := p4Q2PZ37AGS_antipode_dist _ _
    simpa [p4Q2PZ37AGS_signedRationalSphere] using hDist.trans_lt ha

/-- Actual original SU(2) chordal cover, using ADS/ADT's same-group isometry. -/
theorem p4Q2PZ37AHG_originalMesh_cover (N : ℕ) (hN : 0 < N) (g : G) :
    ∃ i : p4Q2PZ37AHG_meshIndex N,
      g ∈ p4Q2PZ37ADK_trueChordalBall (p4Q2PZ37AHG_originalMeshCenter N i) (4 / (N : ℝ)) := by
  obtain ⟨i, hi⟩ := p4Q2PZ37AHG_sphere_mesh_cover N hN (p4Q2PZ37ADR_originalSU2ToSphere g)
  refine ⟨i, ?_⟩
  change p4Q2PZ37ADK_trueChordalDistance
    (p4Q2PZ37ADS_originalSphereToSU2
      (p4Q2PZ37AGS_signedRationalSphere i.1 (p4Q2PZ37AHG_meshParameters N i.2))) g < _
  rw [p4Q2PZ37ADT_originalChordal_eq_sphereDist, p4Q2PZ37ADS_sphere_roundtrip, dist_comm]
  exact hi

/-- Only finite reindexing is classical here; the entire labeled center
family is already explicitly specified and no subcover is selected. -/
def p4Q2PZ37AHG_finCenter (N : ℕ)
    (i : Fin (Fintype.card (p4Q2PZ37AHG_meshIndex N))) : G :=
  p4Q2PZ37AHG_originalMeshCenter N ((Fintype.equivFin (p4Q2PZ37AHG_meshIndex N)).symm i)

theorem p4Q2PZ37AHG_finCover (N : ℕ) (hN : 0 < N) (g : G) :
    ∃ i : Fin (Fintype.card (p4Q2PZ37AHG_meshIndex N)),
      g ∈ p4Q2PZ37ADK_trueChordalBall (p4Q2PZ37AHG_finCenter N i) (4 / (N : ℝ)) := by
  obtain ⟨i, hi⟩ := p4Q2PZ37AHG_originalMesh_cover N hN g
  refine ⟨Fintype.equivFin (p4Q2PZ37AHG_meshIndex N) i, ?_⟩
  simpa only [p4Q2PZ37AHG_finCenter, Equiv.symm_apply_apply] using hi

local instance p4Q2PZ37AHG_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHG_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHG_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHG_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHG_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "pH" => p4Q2PZ37AGN_countRational H
local instance p4Q2PZ37AHG_links : Fintype Link := Fintype.ofFinite _

/-- Original Borel spatial product cells from the specified one-link mesh. -/
def p4Q2PZ37AHG_originalSpatialGrid (N : ℕ) (hN : 0 < N) : p4Q2PZ37AGH_originalSpatialGrid H :=
  p4Q2PZ37AGH_gridOfCover H (Fintype.card (p4Q2PZ37AHG_meshIndex N))
    (p4Q2PZ37AHG_finCenter N) (4 / (N : ℝ))
    (div_pos (by norm_num) (by exact_mod_cast hN)) (p4Q2PZ37AHG_finCover N hN)

def p4Q2PZ37AHG_spatialRadius (N : ℕ) : ℚ := 4 * pH / (N : ℚ)

/-- Sum radius on the ORIGINAL link carrier, using AHF's exact count. -/
theorem p4Q2PZ37AHG_originalSpatialGrid_radius (N : ℕ) (hN : 0 < N) :
    (p4Q2PZ37AHG_originalSpatialGrid H N hN).radius = (p4Q2PZ37AHG_spatialRadius H N : ℝ) := by
  change (Fintype.card Link : ℝ) * (4 / (N : ℝ)) = ((4 * pH / (N : ℚ) : ℚ) : ℝ)
  rw [p4Q2PZ37AHF_count_eq_links H]
  push_cast
  ring

/-- The original rational coordinate Type is retained on every spatial link. -/
def p4Q2PZ37AHG_originalSpatialGrid_coordinates (N : ℕ) (hN : 0 < N)
    (i : Fin (p4Q2PZ37AHG_originalSpatialGrid H N hN).n) (e : Link) :
    p4Q2PZ37AGL_rationalCoordinates ((p4Q2PZ37AHG_originalSpatialGrid H N hN).center i e) := by
  change p4Q2PZ37AGL_rationalCoordinates
    (p4Q2PZ37AHG_finCenter N
      ((Fintype.equivFin (Link → Fin (Fintype.card (p4Q2PZ37AHG_meshIndex N)))).symm i e))
  exact p4Q2PZ37AHG_originalMeshCenter_rational N _

/-- AGQ still selects sound TRUE Haar mass enclosures. The supplied
radius and total mass width remain fields of the actual selected Type. -/
def p4Q2PZ37AHG_explicitPrecisionData
    (N : ℕ) (hN : 0 < N) (eps : ℚ) (heps : 0 < eps) :
    p4Q2PZ37AGU_precisionGridData H (p4Q2PZ37AHG_spatialRadius H N) eps :=
  p4Q2PZ37AGU_precisionDataOfRationalGrid H
    (p4Q2PZ37AHG_originalSpatialGrid H N hN)
    (p4Q2PZ37AHG_originalSpatialGrid_coordinates H N hN)
    (p4Q2PZ37AHG_spatialRadius H N) eps
    (by unfold p4Q2PZ37AHG_spatialRadius p4Q2PZ37AGN_countRational; positivity)
    (p4Q2PZ37AHG_originalSpatialGrid_radius H N hN).le heps

/-- The actual original spatial slice has a positive number of links. -/
theorem p4Q2PZ37AHG_count_pos : (0 : ℚ) < pH := by
  letI : Nonempty Link := ⟨(⟨fun _ => 0, by rfl⟩, ⟨1, by decide⟩)⟩
  rw [p4Q2PZ37AHF_count_eq_links H]
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Link)

theorem p4Q2PZ37AHG_radius128_exact : p4Q2PZ37AHG_spatialRadius H 128 = pH / 32 := by
  norm_num [p4Q2PZ37AHG_spatialRadius] <;> ring

/-- N=128 removes AHF's coarse-radius obstruction, NOT all sign obstacles. -/
theorem p4Q2PZ37AHG_radius128_lt_threshold :
    p4Q2PZ37AHG_spatialRadius H 128 < pH / 24 := by
  rw [p4Q2PZ37AHG_radius128_exact H]
  have hp := p4Q2PZ37AHG_count_pos H
  linarith only [hp]

/-- EVERY actual cell of the specified mesh data is below the necessary
threshold, while preserving the original Haar precision budget. -/
theorem p4Q2PZ37AHG_explicit128_cellRadius_lt
    (eps : ℚ) (heps : 0 < eps)
    (i : Fin (p4Q2PZ37AHG_explicitPrecisionData H 128 (by norm_num) eps heps).data.grid.n) :
    (p4Q2PZ37AHG_explicitPrecisionData H 128 (by norm_num) eps heps).data.radii.radius i < pH / 24 := by
  rw [(p4Q2PZ37AHG_explicitPrecisionData H 128 (by norm_num) eps heps).hCellRadius i]
  exact p4Q2PZ37AHG_radius128_lt_threshold H

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_stereographic_dist_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_stereographic_dist_lt
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_bounded_hemisphere_chart
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_scalar_mesh
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_meshIndex_card
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_mesh128_card
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_originalMeshCenter_rational
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_hemisphere_mesh_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_sphere_mesh_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_originalMesh_cover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHG_finCover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_originalSpatialGrid
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_originalSpatialGrid_radius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_originalSpatialGrid_coordinates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_explicitPrecisionData
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_count_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_radius128_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_radius128_lt_threshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHG_explicit128_cellRadius_lt
