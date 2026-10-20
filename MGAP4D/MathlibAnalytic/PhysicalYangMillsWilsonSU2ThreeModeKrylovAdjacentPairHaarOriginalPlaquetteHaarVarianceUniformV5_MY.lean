import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalPlaquetteTwoSourceFaithfulnessV5_MX
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.HaarFinFourCyclicPlaquetteL2
import MGAP4D.MathlibAnalytic.FiniteProductProbabilityEmbeddingRestrictionL2
import Mathlib.Tactic

/-!
# P4-Q2-MY — ORIGINAL arbitrary SU(2) spatial Wilson plaquette Haar law

MX proved genuine SU(2) Gauss-law Hilbert sources U and W_(H,p) U
are linearly independent for EVERY actual p, but had no quantitative
spatial-volume-independent L² source fluctuation certificate.

MY first proves that all FOUR ACTUAL positively-oriented spatial links
surrounding EVERY original even-periodic spatial plaquette p are distinct,
including the smallest physical even periodic side length 2.

Therefore their actual product spatial Haar reference coordinates project
to four independent SU(2) Haar edge values. The same original
four-edge cyclic holonomy is exactly normalized Haar on SU(2),
by pre-existing *measure-preserving* product-coordinate restriction
and cyclic-Haar-word theorems. The original oriented Wilson plaquette
energy has the same value as the cyclic holonomy, because these group
elements are conjugate, proved by the existing physical Wilson model.

As a result, the ACTUAL spatial Haar distribution of the original
p-local Wilson energy is the SAME as a single genuine SU(2) Haar
Wilson energy for ALL H and ALL p: every continuous real energy test
has exactly the same integral. This is stronger than merely the
pointwise nonconstancy of MV and gives an H-independent positive
genuine Haar variance:
  V_SU2 = ∫_SU2 (WilsonEnergy(g)-HaarMean)^2 d(Haar)(g) > 0,
  ∫_spatial Haar (W_(H,p)(A)-HaarMean)^2 = V_SU2
for every finite H, p.

IMPORTANT: Haar here is ONLY the already existing source-Hilbert
reference measure. This does NOT replace the true interacting
Wilson kernel K_b, its signed two original interacting posteriors,
the source or detector. The conditional K_b-weighted variance may
be smaller and is not claimed H-uniform. No signed GI nondegeneracy,
positive-beta posterior contrast or covariance LOWER bound is derived.
H1-C3, positive-fine arbitrary Krylov separation and continuum gap
remain OPEN.

No artificial Wilson observable, Haar posterior substitution,
Dobrushin, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2MY_leftInvariant :
    Measure.IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2MY_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  unfold normalizedCompactHaar
  infer_instance

namespace GroundStatePosteriorJoint
section PhysicalGeometry
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "mu" => normalizedCompactHaar Gauge
local instance p4Q2MY_linkFintype : Fintype Link := Fintype.ofFinite _

/-- The four REAL oriented positive SU(2) spatial plaquette links in
geometric boundary order, not a surrogate or an arbitrary four-tuple. -/
noncomputable def p4Q2MY_originalPlaquetteFourEdges
    (p : Plaq) : Fin 4 → Link :=
  ![(p.1,p.2.1.1),
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1,p.2.1.2),
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2,p.2.1.1),
    (p.1,p.2.1.2)]

/-- All FOUR positive-link indices of an ACTUAL SU(2) spatial plaquette
are distinct even for the shortest even periodic lattice. This
extends MV's first-edge/non-first-edge proof to all six pairs. -/
theorem p4Q2MY_originalPlaquetteFourEdges_injective
    (p : Plaq) : Function.Injective (p4Q2MY_originalPlaquetteFourEdges H p) := by
  let v := p.1
  let firstAxis := p.2.1.1
  let secondAxis := p.2.1.2
  let e0 : Link := (v,firstAxis)
  let e1 : Link := (periodicHypercubicEvenSpatialSliceShift H v firstAxis,secondAxis)
  let e2 : Link := (periodicHypercubicEvenSpatialSliceShift H v secondAxis,firstAxis)
  let e3 : Link := (v,secondAxis)
  have hAxis : firstAxis ≠ secondAxis := by
    intro h
    exact (ne_of_lt p.2.2) (congrArg Subtype.val h)
  have hShiftMu : periodicHypercubicEvenSpatialSliceShift H v firstAxis ≠ v := by
    intro h
    exact (periodicHypercubicShift_ne_self
      (PeriodicHypercubicEvenSideLength H)
      (by change 2 ≤ 2 * (H + 1); omega)
      v.1 firstAxis.1) (congrArg Subtype.val h)
  have hMV := p4Q2MV_originalSpatialPlaquette_firstLink_otherThree_ne H p
  dsimp only at hMV
  rcases hMV with ⟨h10,h20,h30⟩
  have h01 : e0 ≠ e1 := by exact Ne.symm h10
  have h02 : e0 ≠ e2 := by exact Ne.symm h20
  have h03 : e0 ≠ e3 := by exact Ne.symm h30
  have h12 : e1 ≠ e2 := by
    intro h
    exact hAxis (congrArg Prod.snd h).symm
  have h13 : e1 ≠ e3 := by
    intro h
    exact hShiftMu (congrArg Prod.fst h)
  have h23 : e2 ≠ e3 := by
    intro h
    exact hAxis (congrArg Prod.snd h)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [p4Q2MY_originalPlaquetteFourEdges, e0, e1, e2, e3,
      h01, h02, h03, h12, h13, h23,
      Ne.symm h01, Ne.symm h02, Ne.symm h03,
      Ne.symm h12, Ne.symm h13, Ne.symm h23] at hij ⊢

/-- The selected four real original physical spatial plaquette links
as an index embedding into the COMPLETE spatial SU(2) link carrier. -/
noncomputable def p4Q2MY_originalPlaquetteFourEdgeEmbedding
    (p : Plaq) : Fin 4 ↪ Link :=
  ⟨p4Q2MY_originalPlaquetteFourEdges H p,
    p4Q2MY_originalPlaquetteFourEdges_injective H p⟩

/-- The truly corresponding CYCLIC original four-edge holonomy.
Its energy equals the original oriented physical Wilson energy. -/
noncomputable def p4Q2MY_originalPlaquetteCyclicHolonomy
    (p : Plaq) (A : Cfg) : Gauge :=
  haarFinFourCyclicPlaquetteWord
    (fun k : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p k))

/-- The actual all-spatial-Haar original four-edge cyclic holonomy
has EXACT genuine normalized Haar distribution on SU(2) for ALL p,H.
It uses finite-index restriction and Haar cyclic word invariance,
NOT an independent-Haar replacement for the interacting posterior. -/
theorem p4Q2MY_originalPlaquetteCyclicHolonomy_measurePreserving
    (p : Plaq) :
    MeasurePreserving
      (p4Q2MY_originalPlaquetteCyclicHolonomy H p)
      haar mu := by
  have hcoords :
      MeasurePreserving
        (fun (A : Cfg) (k : Fin 4) =>
          A (p4Q2MY_originalPlaquetteFourEdges H p k))
        haar (Measure.pi fun _ : Fin 4 => mu) := by
    change MeasurePreserving
      (fun (A : Cfg) (k : Fin 4) =>
        A ((p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) k))
      (Measure.pi fun _ : Link => mu)
      (Measure.pi fun _ : Fin 4 => mu)
    exact measurePreserving_finiteProductProbabilityEmbeddingRestriction mu
      (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)
  have hword :
      MeasurePreserving
        (haarFinFourCyclicPlaquetteWord :
          (Fin 4 → Gauge) → Gauge)
        (Measure.pi fun _ : Fin 4 => mu) mu :=
    measurePreserving_haarFinFourCyclicPlaquetteWord mu
  simpa [p4Q2MY_originalPlaquetteCyclicHolonomy,
    Function.comp_def] using hword.comp hcoords

/-- The original ACTUAL oriented SU(2) Wilson plaquette-energy value
is pointwise IDENTICAL to the Haar-cyclic holonomy energy, by the
existing physical-conjugation Wilson identity. -/
theorem p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic
    (p : Plaq) (A : Cfg) :
    p4Q2LO_originalLocalPlaquetteContinuous H p A =
      specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2MY_originalPlaquetteCyclicHolonomy H p A) := by
  have hHol :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p =
        orientedFourEdgePlaquetteWord
          (fun k : Fin 4 =>
            A (p4Q2MY_originalPlaquetteFourEdges H p k)) := by
    rfl
  change specialUnitaryWilsonPlaquetteEnergy 2
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) =
    specialUnitaryWilsonPlaquetteEnergy 2
      (haarFinFourCyclicPlaquetteWord
        (fun k : Fin 4 =>
          A (p4Q2MY_originalPlaquetteFourEdges H p k)))
  rw [hHol]
  exact specialUnitaryWilsonPlaquetteEnergy_orientedFourEdge_eq_cyclic
    (fun k : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p k))

/-- Integral transport of ANY continuous real SU(2) class test through
the ORIGINAL physical plaquette cyclic word under its ACTUAL spatial
Haar carrier: no posterior or kernel replacement. -/
theorem p4Q2MY_originalPlaquetteCyclicHaar_integral_transport
    (p : Plaq) (test : C(Gauge,ℝ)) :
    (∫ A : Cfg,
      test (p4Q2MY_originalPlaquetteCyclicHolonomy H p A) ∂haar) =
      ∫ g : Gauge, test g ∂mu := by
  have hmp :=
    p4Q2MY_originalPlaquetteCyclicHolonomy_measurePreserving H p
  have hchange :=
    integral_map_of_stronglyMeasurable
      (μ := haar) (φ := p4Q2MY_originalPlaquetteCyclicHolonomy H p)
      hmp.measurable test.continuous.stronglyMeasurable
  rw [hmp.map_eq] at hchange
  exact hchange.symm

end PhysicalGeometry

section OriginalHaarVariance
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar Gauge

/-- One fixed genuine SU(2) normalized-Haar Wilson energy mean.
Unlike the K_b-conditional mean, this is independent of H and p. -/
noncomputable def p4Q2MY_singleSU2HaarWilsonMean : ℝ :=
  ∫ g : Gauge, specialUnitaryWilsonPlaquetteEnergy 2 g ∂mu

/-- Fixed strictly positive SU(2) Haar fluctuation benchmark, a
source-side reference-Haar quantity, NOT a receiver/coupling gap. -/
noncomputable def p4Q2MY_singleSU2HaarWilsonVariance : ℝ :=
  ∫ g : Gauge,
    (specialUnitaryWilsonPlaquetteEnergy 2 g -
      p4Q2MY_singleSU2HaarWilsonMean)^2 ∂mu

/-- Strict positivity of the ORIGINAL single-SU(2)-Haar Wilson
variance by two ACTUAL rank-two SU(2) matrices 1 and -I,
using the full topological support of normalized Haar. -/
theorem p4Q2MY_singleSU2HaarWilsonVariance_pos :
    0 < p4Q2MY_singleSU2HaarWilsonVariance := by
  let m : ℝ := p4Q2MY_singleSU2HaarWilsonMean
  let f : Gauge → ℝ :=
    fun g => (specialUnitaryWilsonPlaquetteEnergy 2 g - m)^2
  have hf : Continuous f :=
    ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).sub
      continuous_const).pow 2
  have hi : Integrable f mu :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn : 0 ≤ f := fun g => sq_nonneg _
  have hw : ∃ g : Gauge, f g ≠ 0 := by
    by_cases hm : m = 0
    · refine ⟨specialUnitaryTwoNegativeIdentity, ?_⟩
      change (specialUnitaryWilsonPlaquetteEnergy 2
        specialUnitaryTwoNegativeIdentity - m)^2 ≠ 0
      rw [specialUnitaryWilsonPlaquetteEnergy_two_negativeIdentity, hm]
      norm_num
    · refine ⟨(1 : Gauge), ?_⟩
      change (specialUnitaryWilsonPlaquetteEnergy 2 (1 : Gauge) - m)^2 ≠ 0
      rw [specialUnitaryWilsonPlaquetteEnergy_two_one]
      exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hm))
  rcases hw with ⟨g,hg⟩
  change 0 < ∫ g : Gauge, f g ∂mu
  exact integral_pos_of_integrable_nonneg_nonzero hf hi hn hg

end OriginalHaarVariance

section PhysicalHaarUniversal
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "mu" => normalizedCompactHaar Gauge

/-- Every original SU(2) spatial plaquette on every original finite H
has the EXACT SAME Haar energy test integral as single SU(2) Haar.
A real class function is evaluated against the genuine physical
oriented holonomy energy, never a fake scalar plaquette. -/
theorem p4Q2MY_originalSpatialWilsonEnergy_integral_transport
    (p : Plaq) (test : C(ℝ,ℝ)) :
    (∫ A : Cfg,
      test (p4Q2LO_originalLocalPlaquetteContinuous H p A) ∂haar) =
      (∫ g : Gauge,
        test (specialUnitaryWilsonPlaquetteEnergy 2 g) ∂mu) := by
  let energyTest : C(Gauge,ℝ) :=
    test.comp ⟨specialUnitaryWilsonPlaquetteEnergy 2,
      continuous_specialUnitaryWilsonPlaquetteEnergy 2⟩
  have h :=
    p4Q2MY_originalPlaquetteCyclicHaar_integral_transport H p energyTest
  change
    (∫ A : Cfg,
      test (specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2MY_originalPlaquetteCyclicHolonomy H p A)) ∂haar) =
      (∫ g : Gauge,
        test (specialUnitaryWilsonPlaquetteEnergy 2 g) ∂mu) at h
  calc
    (∫ A : Cfg,
      test (p4Q2LO_originalLocalPlaquetteContinuous H p A) ∂haar) =
      (∫ A : Cfg,
        test (specialUnitaryWilsonPlaquetteEnergy 2
          (p4Q2MY_originalPlaquetteCyclicHolonomy H p A)) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic H p A]
    _ = _ := h

/-- The genuine original spatial-Haar mean of EVERY real SU(2)
Wilson plaquette energy equals ONE universal single-group mean. -/
theorem p4Q2MY_originalSpatialWilsonEnergy_HaarMean_eq_single
    (p : Plaq) :
    (∫ A : Cfg,
      p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar) =
        p4Q2MY_singleSU2HaarWilsonMean := by
  let test : C(ℝ,ℝ) := ⟨id,continuous_id⟩
  simpa only [test, ContinuousMap.coe_mk, id_eq] using
    (p4Q2MY_originalSpatialWilsonEnergy_integral_transport H p test)

/-- The actual original spatial Haar L²-centered Wilson plaquette
square has EXACTLY the same positive norm-square integral as a
single SU(2) Wilson energy, INDEPENDENT of H and the genuine p. -/
theorem p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_eq_single
    (p : Plaq) :
    (∫ A : Cfg,
      (p4Q2LO_originalLocalPlaquetteContinuous H p A -
        p4Q2MY_singleSU2HaarWilsonMean)^2 ∂haar) =
      p4Q2MY_singleSU2HaarWilsonVariance := by
  let test : C(ℝ,ℝ) :=
    ⟨fun x => (x-p4Q2MY_singleSU2HaarWilsonMean)^2,
      ((continuous_id.sub continuous_const).pow 2)⟩
  simpa only [test, ContinuousMap.coe_mk,
    p4Q2MY_singleSU2HaarWilsonVariance] using
    (p4Q2MY_originalSpatialWilsonEnergy_integral_transport H p test)

/-- A genuine VOLUME-UNIFORM POSITIVE reference-Haar fluctuation
benchmark for EVERY actual Wilson p-local SU(2) spatial observable.
Note: this is NOT Var_(K_b)(w_p), which is K-weighted and not yet
known to admit a volume-uniform lower bound. -/
theorem p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_uniform_pos
    (p : Plaq) :
    0 < ∫ A : Cfg,
      (p4Q2LO_originalLocalPlaquetteContinuous H p A -
        p4Q2MY_singleSU2HaarWilsonMean)^2 ∂haar := by
  rw [p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_eq_single H p]
  exact p4Q2MY_singleSU2HaarWilsonVariance_pos

end PhysicalHaarUniversal
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalPlaquetteFourEdges_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalPlaquetteCyclicHolonomy_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalPlaquetteCyclicHaar_integral_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_singleSU2HaarWilsonVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalSpatialWilsonEnergy_integral_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalSpatialWilsonEnergy_HaarMean_eq_single
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_eq_single
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MY_originalSpatialWilsonEnergy_HaarVariance_uniform_pos
