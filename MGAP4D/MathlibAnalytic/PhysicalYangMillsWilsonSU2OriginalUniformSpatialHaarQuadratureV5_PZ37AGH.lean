import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatialChordalCellOscillationV5_PZ37AGG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteBorelHaarCellExistenceV5_PZ37AFN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGH — uniform arbitrary-accuracy original spatial Haar quadrature

Shrinking genuine cells alone does NOT control the sum of rational Haar
mass errors. AGH chooses the geometry first, then the mass tolerance after
the actual number of cells is known. The partition and rational weights
are independent of the right boundary B.

For every fixed H and eps>0, let tau=eps/4 and use genuine SU(2) first-center
cells with per-link radius r=tau/(L_H*card(Link_H)+1). Their true spatial
products have total chordal radius card(Link_H)*r. With M_H the original
AGF integrand envelope, all true center samples satisfy |q_i(B)|<=M_H+tau.
After the product partition has N cells, choose

  delta = tau/(N*(M_H+tau)+1).

The geometry error, center-sampling error and SUMMED mass error are each
at most tau. The total is therefore <=3*eps/4<eps for EVERY original B,
using the SAME geometry and rational Haar weights. The signed transfer is
the unchanged original integral, identified by AGE's true continuous
representative and Haar-a.e. equality, not a new physical observable.

The finite net and rational enclosures still use classical existence.
This is not an evaluated numerical table, an effective complexity bound,
a nonzero transfer sign, a two-sign shell, volume-uniform coercivity,
a Hamiltonian spectral gap, or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Normalize a finite accumulated error without requiring x>0.
The added one also covers zero links and zero amplitudes. -/
theorem p4Q2PZ37AGH_normalizedBudget_le
    (x tau : ℝ) (hx : 0 ≤ x) (htau : 0 ≤ tau) :
    x * (tau / (x + 1)) ≤ tau := by
  have hden : 0 < x + 1 := by linarith only [hx]
  calc
    x * (tau / (x + 1)) = (x * tau) / (x + 1) := by ring
    _ ≤ tau := (div_le_iff₀ hden).mpr (by nlinarith only [htau])

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local instance p4Q2PZ37AGH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGH_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGH_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGH_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGH_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "slope" => p4Q2PZ37AGG_originalSpatialSlope H
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGH_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Geometry and true Haar measurability are independent of all rational
mass approximations. Centers need not belong to first-center cells. -/
structure p4Q2PZ37AGH_originalSpatialGrid (H : ℕ) where
  n : ℕ
  cell : Fin n → Set
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
  hMeas : ∀ i, MeasurableSet (cell i)
  hPartition :
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ∃ i : Fin n, A ∈ cell i ∧ ∀ j : Fin n, A ∈ cell j → j = i
  center : Fin n →
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  hRadius : ∀ i A, A ∈ cell i →
    p4Q2PZ37AGG_originalSpatialChordalDistance H A (center i) ≤ radius

/-- Products of actual AFN first-center SU(2) Borel cells on the ORIGINAL
spatial link carrier, at an arbitrary supplied genuine radius. -/
def p4Q2PZ37AGH_productCell
    (n : ℕ) (centers : Fin n → G) (r : ℝ)
    (index : Link → Fin n) : Set Cfg :=
  Set.univ.pi (fun e : Link =>
    p4Q2PZ37AFN_originalFirstCenterCell n centers r (index e))

theorem p4Q2PZ37AGH_productCell_measurable
    (n : ℕ) (centers : Fin n → G) (r : ℝ) (index : Link → Fin n) :
    MeasurableSet (p4Q2PZ37AGH_productCell H n centers r index) := by
  unfold p4Q2PZ37AGH_productCell
  exact MeasurableSet.univ_pi (fun e : Link =>
    p4Q2PZ37AFN_originalFirstCenterCell_measurable n centers r (index e))

theorem p4Q2PZ37AGH_productCells_partition
    (n : ℕ) (centers : Fin n → G) (r : ℝ)
    (hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r)
    (A : Cfg) :
    ∃ index : Link → Fin n,
      A ∈ p4Q2PZ37AGH_productCell H n centers r index ∧
      ∀ next : Link → Fin n,
        A ∈ p4Q2PZ37AGH_productCell H n centers r next → next = index := by
  classical
  have hPart := p4Q2PZ37AFN_originalFirstCenterCell_partition n centers r hCover
  let index : Link → Fin n := fun e => Classical.choose (hPart (A e))
  have hmem (e : Link) :
      A e ∈ p4Q2PZ37AFN_originalFirstCenterCell n centers r (index e) :=
    (Classical.choose_spec (hPart (A e))).1
  refine ⟨index, Set.mem_univ_pi.mpr hmem, ?_⟩
  intro next hnext
  funext e
  exact (Classical.choose_spec (hPart (A e))).2 (next e)
    ((Set.mem_univ_pi.mp hnext) e)

/-- Sum the true per-link chordal radii; no dimension-free radius is
silently substituted for the actual spatial l1 distance. -/
theorem p4Q2PZ37AGH_productCell_distance
    (n : ℕ) (centers : Fin n → G) (r : ℝ)
    (index : Link → Fin n) (A : Cfg)
    (hA : A ∈ p4Q2PZ37AGH_productCell H n centers r index) :
    Dsp A (fun e => centers (index e)) ≤ (Fintype.card Link : ℝ) * r := by
  change A ∈ Set.univ.pi (fun e : Link =>
    p4Q2PZ37AFN_originalFirstCenterCell n centers r (index e)) at hA
  unfold p4Q2PZ37AGG_originalSpatialChordalDistance
  calc
    (∑ e : Link, dJ (A e) (centers (index e))) ≤ ∑ _e : Link, r := by
      apply Finset.sum_le_sum
      intro e _he
      have hCell := (Set.mem_univ_pi.mp hA) e
      have hBall :=
        ((p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
          n centers r (index e) (A e)).mp hCell).1
      change dJ (centers (index e)) (A e) < r at hBall
      rw [p4Q2PZ37ADK_trueChordalDistance_symm]
      exact hBall.le
    _ = (Fintype.card Link : ℝ) * r := by simp

/-- A genuine finite one-link cover gives a finite original spatial
partition with exactly the certified sum radius. -/
def p4Q2PZ37AGH_gridOfCover
    (n : ℕ) (centers : Fin n → G) (r : ℝ) (hr : 0 < r)
    (hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r) :
    p4Q2PZ37AGH_originalSpatialGrid H := by
  classical
  let I := Link → Fin n
  let E := Fintype.equivFin I
  refine {
    n := Fintype.card I
    cell := fun i => p4Q2PZ37AGH_productCell H n centers r (E.symm i)
    hMeas := fun i => p4Q2PZ37AGH_productCell_measurable H n centers r (E.symm i)
    hPartition := ?_
    center := fun i e => centers (E.symm i e)
    radius := (Fintype.card Link : ℝ) * r
    radius_nonneg := mul_nonneg (Nat.cast_nonneg _) hr.le
    hRadius := ?_ }
  · intro A
    obtain ⟨index, hindex, hOnly⟩ :=
      p4Q2PZ37AGH_productCells_partition H n centers r hCover A
    refine ⟨E index, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hindex
    · intro j hj
      apply E.symm.injective
      simpa only [Equiv.symm_apply_apply] using hOnly (E.symm j) hj
  · intro i A hA
    exact p4Q2PZ37AGH_productCell_distance H n centers r (E.symm i) A hA

/-- Arbitrarily fine genuine spatial products exist for every positive
one-link radius, without an external modulus or artificial Haar law. -/
theorem p4Q2PZ37AGH_exists_fineSpatialGrid
    (r : ℝ) (hr : 0 < r) :
    ∃ grid : p4Q2PZ37AGH_originalSpatialGrid H,
      grid.radius = (Fintype.card Link : ℝ) * r := by
  classical
  obtain ⟨s, hNet⟩ := p4Q2PZ37ADP_exists_trueFiniteChordalNet r hr
  let n : ℕ := s.card
  let centers : Fin n → G := fun i => ((Finset.equivFin s).symm i).1
  have hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r := by
    intro g
    obtain ⟨a, ha, hag⟩ := hNet g
    refine ⟨Finset.equivFin s ⟨a, ha⟩, ?_⟩
    simpa [n, centers, p4Q2PZ37ADK_trueChordalBall] using hag
  exact ⟨p4Q2PZ37AGH_gridOfCover H n centers r hr hCover, rfl⟩

/-- Choose rational approximations to the ACTUAL spatial Haar masses
only after the geometry and desired mass precision have been selected. -/
def p4Q2PZ37AGH_massCells
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (delta : ℝ) (hdelta : 0 < delta) : p4Q2PZ37AGC_originalHaarCells H where
  n := grid.n
  cell := grid.cell
  hMeas := grid.hMeas
  hPartition := grid.hPartition
  weight := fun i => p4Q2PZ37AFN_rationalEnclosure
    (Measure.real muH (grid.cell i)) delta hdelta
  weightError := fun _ => delta
  hWeightError_nonneg := fun _ => hdelta.le
  hWeightAccuracy := fun i => p4Q2PZ37AFN_rationalEnclosure_error
    (Measure.real muH (grid.cell i)) delta hdelta

/-- The authentic AGF bound is uniform over BOTH original configurations. -/
def p4Q2PZ37AGH_originalEnvelope : ℝ := ((1 - kFloor) / 2) * pH

theorem p4Q2PZ37AGH_originalEnvelope_nonneg :
    0 ≤ p4Q2PZ37AGH_originalEnvelope H :=
  mul_nonneg (p4Q2PZ37AGB_originalKernel_radius_nonneg H)
    (p4Q2PZ37AGF_plaquetteCount_nonneg H)

/-- Rational enclosures sample true continuous center values, not an
arbitrary Haar-L2 representative and not the unknown integral itself. -/
def p4Q2PZ37AGH_originalSample
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau : ℝ) (htau : 0 < tau) (i : Fin grid.n) : ℚ :=
  p4Q2PZ37AFN_rationalEnclosure (gCont B (grid.center i)) tau htau

theorem p4Q2PZ37AGH_originalSample_accuracy
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau : ℝ) (htau : 0 < tau) (i : Fin grid.n) :
    |gCont B (grid.center i) -
      (p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| ≤ tau :=
  p4Q2PZ37AFN_rationalEnclosure_error (gCont B (grid.center i)) tau htau

/-- Uniform sample amplitude makes a B-independent mass budget possible. -/
theorem p4Q2PZ37AGH_originalSample_abs_le
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau : ℝ) (htau : 0 < tau) (i : Fin grid.n) :
    |(p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| ≤
      p4Q2PZ37AGH_originalEnvelope H + tau := by
  have hs := p4Q2PZ37AGH_originalSample_accuracy H grid B tau htau i
  have hm := p4Q2PZ37AGF_originalContinuousIntegrand_abs_le_floor H B (grid.center i)
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
  unfold p4Q2PZ37AGH_originalEnvelope
  apply abs_le.mpr
  constructor <;> linarith only [hslo, hshi, hmlo, hmhi]

/-- The full sum of mass errors, including the actual cell count. -/
theorem p4Q2PZ37AGH_summedMassError_le
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau delta : ℝ) (htau : 0 < tau) (hdelta : 0 < delta) :
    p4Q2PZ37AGC_HaarWeightError (p4Q2PZ37AGH_massCells H grid delta hdelta)
      (p4Q2PZ37AGH_originalSample H grid B tau htau) ≤
      (grid.n : ℝ) * (p4Q2PZ37AGH_originalEnvelope H + tau) * delta := by
  change (∑ i : Fin grid.n,
      |(p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| * delta) ≤ _
  calc
    (∑ i : Fin grid.n,
        |(p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| * delta) ≤
      ∑ _i : Fin grid.n, (p4Q2PZ37AGH_originalEnvelope H + tau) * delta := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_right
          (p4Q2PZ37AGH_originalSample_abs_le H grid B tau htau i) hdelta.le
    _ = (grid.n : ℝ) * (p4Q2PZ37AGH_originalEnvelope H + tau) * delta := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Geometry and center sampling control every point of the genuine cell. -/
theorem p4Q2PZ37AGH_cellwiseSample_accuracy
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau : ℝ) (htau : 0 < tau) (i : Fin grid.n) (A : Cfg)
    (hA : A ∈ grid.cell i) :
    |gCont B A - (p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| ≤
      slope * grid.radius + tau := by
  have hOsc :=
    (p4Q2PZ37AGG_originalContinuousIntegrand_allLinkChordalSlope
      H B A (grid.center i)).trans
      (mul_le_mul_of_nonneg_left (grid.hRadius i A hA)
        (p4Q2PZ37AGG_originalSpatialSlope_nonneg H))
  exact (abs_sub_le _ (gCont B (grid.center i)) _).trans
    (add_le_add hOsc (p4Q2PZ37AGH_originalSample_accuracy H grid B tau htau i))

/-- All three genuine errors are exposed: geometry, rational center
sampling, and the whole sum of true Haar mass errors. -/
theorem p4Q2PZ37AGH_originalTransfer_threeErrorBound
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) (B : Cfg)
    (tau delta : ℝ) (htau : 0 < tau) (hdelta : 0 < delta) :
    |t B - (p4Q2PZ37AGC_HaarCenter
      (p4Q2PZ37AGH_massCells H grid delta hdelta)
      (p4Q2PZ37AGH_originalSample H grid B tau htau) : ℝ)| ≤
      slope * grid.radius + tau +
        (grid.n : ℝ) * (p4Q2PZ37AGH_originalEnvelope H + tau) * delta := by
  have hInt : Integrable (gCont B) muH :=
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable B).congr
      (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H B)
  have hLocal : ∀ i : Fin grid.n, ∀ A : Cfg, A ∈ grid.cell i →
      |gCont B A - (p4Q2PZ37AGH_originalSample H grid B tau htau i : ℝ)| ≤
        slope * grid.radius + tau := by
    intro i A hA
    exact p4Q2PZ37AGH_cellwiseSample_accuracy H grid B tau htau i A hA
  have h := p4Q2PZ37AGC_integral_error_of_cells
    (p4Q2PZ37AGH_massCells H grid delta hdelta)
    (gCont B) (p4Q2PZ37AGH_originalSample H grid B tau htau)
    (slope * grid.radius + tau) hInt hLocal
  rw [p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H B] at h
  exact h.trans (add_le_add_left
    (p4Q2PZ37AGH_summedMassError_le H grid B tau delta htau hdelta)
    (slope * grid.radius + tau))

/-- A single B-independent spatial geometry and mass precision whose
certified true error budget is strictly below the requested tolerance. -/
structure p4Q2PZ37AGH_originalUniformQuadrature (H : ℕ) (eps : ℝ) where
  grid : p4Q2PZ37AGH_originalSpatialGrid H
  sampleTolerance : ℝ
  massTolerance : ℝ
  sampleTolerance_pos : 0 < sampleTolerance
  massTolerance_pos : 0 < massTolerance
  hBudget : p4Q2PZ37AGG_originalSpatialSlope H * grid.radius + sampleTolerance +
    (grid.n : ℝ) * (p4Q2PZ37AGH_originalEnvelope H + sampleTolerance) *
      massTolerance < eps

/-- No physical oracle: fine geometry is chosen first; its actual cell
count is then used to shrink the SUM of mass approximation errors. -/
theorem p4Q2PZ37AGH_exists_uniformQuadrature
    (eps : ℝ) (heps : 0 < eps) :
    Nonempty (p4Q2PZ37AGH_originalUniformQuadrature H eps) := by
  let tau := eps / 4
  have htau : 0 < tau := by dsimp [tau]; positivity
  let a : ℝ := slope * (Fintype.card Link : ℝ)
  have ha : 0 ≤ a := mul_nonneg
    (p4Q2PZ37AGG_originalSpatialSlope_nonneg H) (Nat.cast_nonneg _)
  let r : ℝ := tau / (a + 1)
  have hr : 0 < r := div_pos htau (by linarith only [ha])
  obtain ⟨grid, hRadius⟩ := p4Q2PZ37AGH_exists_fineSpatialGrid H r hr
  have hGeometry : slope * grid.radius ≤ tau := by
    rw [hRadius]
    calc
      slope * ((Fintype.card Link : ℝ) * r) = a * (tau / (a + 1)) := by
        dsimp [a, r]
        ring
      _ ≤ tau := p4Q2PZ37AGH_normalizedBudget_le a tau ha htau.le
  let b : ℝ := (grid.n : ℝ) * (p4Q2PZ37AGH_originalEnvelope H + tau)
  have hb : 0 ≤ b := mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (p4Q2PZ37AGH_originalEnvelope_nonneg H) htau.le)
  let delta : ℝ := tau / (b + 1)
  have hdelta : 0 < delta := div_pos htau (by linarith only [hb])
  have hMass : b * delta ≤ tau := p4Q2PZ37AGH_normalizedBudget_le b tau hb htau.le
  refine ⟨{
    grid := grid
    sampleTolerance := tau
    massTolerance := delta
    sampleTolerance_pos := htau
    massTolerance_pos := hdelta
    hBudget := ?_ }⟩
  change slope * grid.radius + tau + b * delta < eps
  calc
    slope * grid.radius + tau + b * delta ≤ tau + tau + tau :=
      add_le_add (add_le_add_right hGeometry tau) hMass
    _ < eps := by dsimp [tau]; linarith only [heps]

/-- EVERY original right boundary is certified by the SAME chosen
partition and rational Haar weights. Only center-value samples vary. -/
theorem p4Q2PZ37AGH_uniformQuadrature_accuracy
    {eps : ℝ} (c : p4Q2PZ37AGH_originalUniformQuadrature H eps) (B : Cfg) :
    |t B - (p4Q2PZ37AGC_HaarCenter
      (p4Q2PZ37AGH_massCells H c.grid c.massTolerance c.massTolerance_pos)
      (p4Q2PZ37AGH_originalSample H c.grid B
        c.sampleTolerance c.sampleTolerance_pos) : ℝ)| < eps :=
  (p4Q2PZ37AGH_originalTransfer_threeErrorBound H c.grid B
    c.sampleTolerance c.massTolerance c.sampleTolerance_pos c.massTolerance_pos).trans_lt
      c.hBudget

/-- Retain AGA's exact rational-ball semantics with a genuine finite
quadrature center and any positive requested rational radius. -/
def p4Q2PZ37AGH_originalTransferRationalBall
    (radius : ℚ) (hradius : 0 < radius)
    (c : p4Q2PZ37AGH_originalUniformQuadrature H (radius : ℝ)) (B : Cfg) :
    p4Q2PZ37AGA_rationalBall (t B) where
  sample := p4Q2PZ37AGC_HaarCenter
    (p4Q2PZ37AGH_massCells H c.grid c.massTolerance c.massTolerance_pos)
    (p4Q2PZ37AGH_originalSample H c.grid B
      c.sampleTolerance c.sampleTolerance_pos)
  radius := radius
  radius_nonneg := hradius.le
  hContains := (p4Q2PZ37AGH_uniformQuadrature_accuracy H c B).le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGH_normalizedBudget_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_productCell_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_productCells_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_productCell_distance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_gridOfCover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_exists_fineSpatialGrid
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_massCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_originalEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_originalSample_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_originalSample_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_summedMassError_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_cellwiseSample_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_originalTransfer_threeErrorBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_exists_uniformQuadrature
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_uniformQuadrature_accuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGH_originalTransferRationalBall
