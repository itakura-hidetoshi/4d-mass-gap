import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitStereographicMeshV5_PZ37AHG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullOneSlabStrictTransferV5_LJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHH — unconditional original nonzero rational sign existence

The original ZW centered physical source, NOT JU's anchored alternative,
has continuous representative f=(W-p_H)/2. Its value at the actual identity
configuration is -p_H/2<0, since AHG proved p_H>0. The existing LJ strict
positivity theorem for the FULL original Wilson kernel (including both
spatial halfweights) therefore applies without a new nonzero premise.

This proves, for EVERY H, that the SAME original physical transfer is
nonzero at some actual boundary. AEV's true one-link slope and AGG's finite
coordinate telescoping bound its variation. AHG's explicitly specified
rational boundary meshes approximate that nonzero boundary closely enough
at some finite order N>96, so a rational-coordinate boundary with nonzero
original transfer EXISTS. AHE completeness then proves existence of an
accepting original AGU/AGP signed-Haar rational table. AHF additionally
forces the selected integration radius R<p_H/24.

The existence statements are unconditional for the unchanged model, but
no numerical N, boundary assignment, sign branch, mass table or accepting
Boolean evaluation is extracted. The right-boundary AHG mesh and the
left-integration AGU grid are DIFFERENT finite data and are not identified.
No two-sign shell, volume-uniform coercivity or continuum mass gap follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A finite mesh order defeats any fixed finite nonnegative variation
budget. No effective bound on a subsequently chosen physical margin is
asserted. The 96 cutoff also keeps the AHG boundary mesh subcritical. -/
theorem p4Q2PZ37AHH_exists_meshOrder
    (C L s : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hs : 0 < s) :
    ∃ N : ℕ, 96 < N ∧ C * (L * (4 / (N : ℝ))) < s := by
  have hq : 0 ≤ 4 * C * L / s :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hL) hs.le
  obtain ⟨N, hN⟩ := exists_nat_gt (97 + 4 * C * L / s)
  have hLarge : (96 : ℝ) < (N : ℝ) := by linarith only [hN, hq]
  have hNnat : 96 < N := by exact_mod_cast hLarge
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith only [hLarge]
  have hQuot : 4 * C * L / s < (N : ℝ) := by linarith only [hN]
  have hNum : 4 * C * L < (N : ℝ) * s := (div_lt_iff₀ hs).mp hQuot
  refine ⟨N, hNnat, ?_⟩
  calc
    C * (L * (4 / (N : ℝ))) = (4 * C * L) / (N : ℝ) := by ring
    _ < s := (div_lt_iff₀ hNr).mpr (by nlinarith only [hNum])

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHH_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHH_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHH_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHH_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHH_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AHH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHH_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The original continuous centered action has an explicit nonzero
value. No point value of an arbitrary L2 representative is used. -/
theorem p4Q2PZ37AHH_originalSource_identity :
    fCont (fun _ : Link => (1 : G)) = -pH / 2 := by
  have hW : periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
      (fun _ : Link => (1 : G)) = 0 := by
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
      specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H]
  change (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
    (fun _ : Link => (1 : G)) - pH) / 2 = -pH / 2
  rw [hW]
  ring

/-- Nonzeroness of the ACTUAL ZW continuous representative is proved,
not passed as an external hypothesis to a conditional transfer theorem. -/
theorem p4Q2PZ37AHH_originalSource_ne_zero : fCont ≠ 0 := by
  have hp : (0 : ℝ) < pH := by
    rw [← p4Q2PZ37AGN_countRational_exact H]
    exact_mod_cast p4Q2PZ37AHG_count_pos H
  intro hz
  have hAt := congrArg (fun f : C(Cfg, ℝ) => f (fun _ : Link => (1 : G))) hz
  rw [p4Q2PZ37AHH_originalSource_identity H, ContinuousMap.zero_apply] at hAt
  linarith only [hp, hAt]

/-- Strict full-kernel Haar energy of THIS unchanged centered source.
The original positive spatial halfweights remain in K. -/
theorem p4Q2PZ37AHH_originalSource_fullQuadratic_pos :
    0 < (∫ A : Cfg, ∫ B : Cfg, K A B * (fCont A * fCont B) ∂muH ∂muH) :=
  p4Q2LJ_originalFullWilsonOneSlabHaarDoubleIntegral_pos H fCont
    (p4Q2PZ37AHH_originalSource_ne_zero H) b0 p4Q2PZ37ADC_fixedCoupling_pos

/-- UNCONDITIONAL existence for the literal original ZW physical source
at the literal original fixed positive coupling, for every finite H. -/
theorem p4Q2PZ37AHH_originalTransfer_exists_nonzero :
    ∃ B : Cfg, t B ≠ 0 :=
  p4Q2LJ_originalPhysicalTransfer_exists_nonzero_of_continuousRepresentative
    H b0 p4Q2PZ37ADC_fixedCoupling_pos f0 fCont
    (p4Q2PZ37AFZ_originalCenteredSource_eq_toLp H)
    (p4Q2PZ37AHH_originalSource_ne_zero H)

/-- Genuine finite source-dependent right-boundary slope, not a supplied
modulus for a substituted transfer. -/
def p4Q2PZ37AHH_transferSlope : ℝ :=
  (13 * b0) * p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H

theorem p4Q2PZ37AHH_transferSlope_nonneg : 0 ≤ p4Q2PZ37AHH_transferSlope H := by
  unfold p4Q2PZ37AHH_transferSlope
  exact mul_nonneg (mul_nonneg (by norm_num) p4Q2PZ37ADC_fixedCoupling_pos.le)
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

/-- AEV one-link control descends along the original finite link carrier. -/
theorem p4Q2PZ37AHH_originalTransfer_allLinkSlope (B C : Cfg) :
    |t B - t C| ≤ p4Q2PZ37AHH_transferSlope H *
      p4Q2PZ37AGG_originalSpatialChordalDistance H B C := by
  exact p4Q2PZ37AGG_finiteCoordinate_absLipschitz dJ
    p4Q2PZ37ADK_trueChordalDistance_symm (p4Q2PZ37AHH_transferSlope H) t
    (fun u i g h => p4Q2PZ37AEV_originalCenteredTransfer_rightOneLinkChordSlope H u i g h) B C

/-- RIGHT boundary mesh, distinct from the LEFT Haar integration grid. -/
def p4Q2PZ37AHH_meshBoundary (N : ℕ)
    (a : Link → p4Q2PZ37AHG_meshIndex N) : Cfg :=
  fun e => p4Q2PZ37AHG_originalMeshCenter N (a e)

def p4Q2PZ37AHH_meshBoundary_coordinates (N : ℕ)
    (a : Link → p4Q2PZ37AHG_meshIndex N) :
    ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (p4Q2PZ37AHH_meshBoundary H N a e) :=
  fun e => p4Q2PZ37AHG_originalMeshCenter_rational N (a e)

/-- Every original boundary is approximated by the explicitly specified
AHG rational family, with the actual full-transfer variation bound. -/
theorem p4Q2PZ37AHH_originalTransfer_meshApproximation
    (B : Cfg) (N : ℕ) (hN : 0 < N) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      |t B - t (p4Q2PZ37AHH_meshBoundary H N a)| ≤
        p4Q2PZ37AHH_transferSlope H * ((Fintype.card Link : ℝ) * (4 / (N : ℝ))) := by
  choose a ha using (fun e : Link => p4Q2PZ37AHG_originalMesh_cover N hN (B e))
  have hEach (e : Link) :
      dJ (B e) (p4Q2PZ37AHH_meshBoundary H N a e) ≤ 4 / (N : ℝ) := by
    have h := ha e
    change dJ (p4Q2PZ37AHG_originalMeshCenter N (a e)) (B e) < 4 / (N : ℝ) at h
    rw [p4Q2PZ37ADK_trueChordalDistance_symm] at h
    exact h.le
  have hSum : p4Q2PZ37AGG_originalSpatialChordalDistance H B
      (p4Q2PZ37AHH_meshBoundary H N a) ≤ (Fintype.card Link : ℝ) * (4 / (N : ℝ)) := by
    unfold p4Q2PZ37AGG_originalSpatialChordalDistance
    calc
      (∑ e : Link, dJ (B e) (p4Q2PZ37AHH_meshBoundary H N a e)) ≤
          ∑ _e : Link, 4 / (N : ℝ) := Finset.sum_le_sum (fun e _ => hEach e)
      _ = (Fintype.card Link : ℝ) * (4 / (N : ℝ)) := by simp
  exact ⟨a, (p4Q2PZ37AHH_originalTransfer_allLinkSlope H B _).trans
    (mul_le_mul_of_nonneg_left hSum (p4Q2PZ37AHH_transferSlope_nonneg H))⟩

/-- Some finite rational AHG right boundary has NONZERO original transfer.
The proof does not output an evaluated order, label assignment, or sign. -/
theorem p4Q2PZ37AHH_exists_meshBoundary_nonzero :
    ∃ N : ℕ, 96 < N ∧ ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      t (p4Q2PZ37AHH_meshBoundary H N a) ≠ 0 := by
  obtain ⟨B, hB⟩ := p4Q2PZ37AHH_originalTransfer_exists_nonzero H
  have hAbs : 0 < |t B| := abs_pos.mpr hB
  obtain ⟨N, hN, hError⟩ := p4Q2PZ37AHH_exists_meshOrder
    (p4Q2PZ37AHH_transferSlope H) (Fintype.card Link : ℝ) (|t B| / 2)
    (p4Q2PZ37AHH_transferSlope_nonneg H) (Nat.cast_nonneg _)
    (div_pos hAbs (by norm_num))
  obtain ⟨a, ha⟩ := p4Q2PZ37AHH_originalTransfer_meshApproximation H B N (by omega)
  refine ⟨N, hN, a, ?_⟩
  intro hz
  have hClose := ha.trans_lt hError
  rw [hz, sub_zero] at hClose
  linarith only [hClose, hAbs]

/-- Existential evidence in the original AGL rational-coordinate Type,
not merely density in a different configuration space. -/
theorem p4Q2PZ37AHH_exists_rationalBoundary_nonzero :
    ∃ B : Cfg, Nonempty (∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) ∧ t B ≠ 0 := by
  obtain ⟨N, _hN, a, ha⟩ := p4Q2PZ37AHH_exists_meshBoundary_nonzero H
  exact ⟨p4Q2PZ37AHH_meshBoundary H N a,
    ⟨p4Q2PZ37AHH_meshBoundary_coordinates H N a⟩, ha⟩

/-- AHE completeness now yields an UNCONDITIONAL existential sign
certificate for the original model, rather than assuming a nonzero t. -/
theorem p4Q2PZ37AHH_exists_meshBoundary_signCertificate :
    ∃ N : ℕ, 96 < N ∧ ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      p4Q2PZ37AHE_finePositiveCertificate H (p4Q2PZ37AHH_meshBoundary H N a)
        (p4Q2PZ37AHH_meshBoundary_coordinates H N a) ∨
      p4Q2PZ37AHE_fineNegativeCertificate H (p4Q2PZ37AHH_meshBoundary H N a)
        (p4Q2PZ37AHH_meshBoundary_coordinates H N a) := by
  obtain ⟨N, hN, a, ha⟩ := p4Q2PZ37AHH_exists_meshBoundary_nonzero H
  exact ⟨N, hN, a, (p4Q2PZ37AHE_fineSign_iff_nonzero H
    (p4Q2PZ37AHH_meshBoundary H N a) (p4Q2PZ37AHH_meshBoundary_coordinates H N a)).mpr ha⟩

/-- An actual finite original AGU/AGP table accepts at some rational
right boundary. Its integration radius is strictly below p_H/24 by AHF.
Neither the unknown sign nor the true Haar mass data are numerically evaluated. -/
theorem p4Q2PZ37AHH_exists_acceptingOriginalTable :
    ∃ N : ℕ, 96 < N ∧ ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
    ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      R < p4Q2PZ37AGN_countRational H / 24 ∧
      (p4Q2PZ37AHE_originalPositiveCheck H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        (p4Q2PZ37AHH_meshBoundary H N a) (p4Q2PZ37AHH_meshBoundary_coordinates H N a) m n hn = true ∨
       p4Q2PZ37AHE_originalNegativeCheck H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        (p4Q2PZ37AHH_meshBoundary H N a) (p4Q2PZ37AHH_meshBoundary_coordinates H N a) m n hn = true) := by
  obtain ⟨N, hN, a, hSign⟩ := p4Q2PZ37AHH_exists_meshBoundary_signCertificate H
  rcases hSign with hPos | hNeg
  · obtain ⟨R, eps, hR, heps, m, n, hn, hc⟩ := hPos
    refine ⟨N, hN, a, R, eps, hR, heps, m, n, hn, ?_, Or.inl hc⟩
    exact p4Q2PZ37AHF_precision_accepting_radius_lt H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps)
      (p4Q2PZ37AHH_meshBoundary H N a) (p4Q2PZ37AHH_meshBoundary_coordinates H N a)
      m n hn (Or.inl hc)
  · obtain ⟨R, eps, hR, heps, m, n, hn, hc⟩ := hNeg
    refine ⟨N, hN, a, R, eps, hR, heps, m, n, hn, ?_, Or.inr hc⟩
    exact p4Q2PZ37AHF_precision_accepting_radius_lt H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps)
      (p4Q2PZ37AHH_meshBoundary H N a) (p4Q2PZ37AHH_meshBoundary_coordinates H N a)
      m n hn (Or.inr hc)

/-- Literal raw AGP endpoint existence, with the original physics and
proof-carrying Haar data: this is NOT an evaluated finite witness. -/
theorem p4Q2PZ37AHH_exists_strictOriginalHaarTable :
    ∃ B : Cfg, ∃ b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e),
    ∃ d : p4Q2PZ37AGP_gridData H, ∃ m n : ℕ, ∃ hn : 0 < n,
      0 < (p4Q2PZ37AGP_originalTable H d B b m n hn).lower ∨
        (p4Q2PZ37AGP_originalTable H d B b m n hn).upper < 0 := by
  obtain ⟨N, _hN, a, R, eps, hR, heps, m, n, hn, _hSmall, hc⟩ :=
    p4Q2PZ37AHH_exists_acceptingOriginalTable H
  let B := p4Q2PZ37AHH_meshBoundary H N a
  let b := p4Q2PZ37AHH_meshBoundary_coordinates H N a
  let d := (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
  have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
  refine ⟨B, b, d, m, n, hn, ?_⟩
  rcases hc with hp | hn'
  · exact Or.inl ((p4Q2PZ37AHE_positiveCheck_iff _ hMass).mp hp)
  · exact Or.inr ((p4Q2PZ37AHE_negativeCheck_iff _ hMass).mp hn')

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHH_exists_meshOrder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalSource_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalSource_fullQuadratic_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalTransfer_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_transferSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalTransfer_allLinkSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_meshBoundary_coordinates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_originalTransfer_meshApproximation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_exists_meshBoundary_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_exists_rationalBoundary_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_exists_meshBoundary_signCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_exists_acceptingOriginalTable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHH_exists_strictOriginalHaarTable
