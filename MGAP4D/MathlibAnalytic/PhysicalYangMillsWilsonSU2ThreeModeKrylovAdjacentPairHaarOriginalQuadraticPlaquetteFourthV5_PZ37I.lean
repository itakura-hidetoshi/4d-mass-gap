import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllPowerTwoCrossingWardV5_PZ37H
import Mathlib.Tactic

/-!
# P4-Q2-PZ37I — genuine spatial plaquette-pair fourth Haar obstruction

Keep the original finite-period SU(2) Wilson action, full temporal crossing
and normalized product spatial Haar. Since the true spatial half-action is
w=(N_P-Φ)/2 with Φ the SUM of original plaquette characters, its square
has a constant term, a term linear in the original spatial action, and
one genuine quadratic trace term. The first is Haar boundary-invariant;
the second is affine in w by the already-proved genuine F(1,4) Schur slope.

Thus only the actual quadratic original spatial-plaquette trace Haar
moment K(B)=integral Φ(X)^2 Cross(X,B)^4 can contribute to the
alternating physical seventh coefficient. We expand K into EVERY ordered
pair of original spatial plaquettes, including the diagonal and period-2
overlaps. No pair, physical posterior, or Haar integral is replaced or
silently discarded; the remaining obstruction is not presumed zero.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37I_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37I_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37I_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37I_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37I_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37I_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37I_plaquettesFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ37I_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalQuadraticFourth
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "F" => p4Q2PZ37D_originalMixedHaar H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))

/-- Literal finite cardinality of the ORIGINAL spatial plaquette carrier. -/
noncomputable def p4Q2PZ37I_originalPlaquetteCount : ℝ :=
  (Fintype.card Plaq : ℝ)
local notation "NP" => p4Q2PZ37I_originalPlaquetteCount H

/-- Genuine two-plaquette spatial trace insertion against the COMPLETE
fourth temporal crossing; no independence of the two plaquettes. -/
noncomputable def p4Q2PZ37I_originalPairTraceFourth
    (p q : Plaq) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (χ p X*χ q X)*(Cross X B)^4 ∂haar

local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H

/-- The surviving full two-plaquette insertion BEFORE any geometry/parity
selection. No claims about its sign or spatial-boundary factorization. -/
noncomputable def p4Q2PZ37I_originalQuadraticTraceFourth
    (B : Cfg) : ℝ :=
  ∫ X : Cfg, (Φ X)^2*(Cross X B)^4 ∂haar

local notation "K4" => p4Q2PZ37I_originalQuadraticTraceFourth H

/-- The true original spatial half-Wilson action equals half the
original plaquette count minus half the full original character sum. -/
theorem p4Q2PZ37I_originalHalfAction_card_sub_trace (X : Cfg) :
    w X = (NP-Φ X)/2 := by
  unfold p4Q2PS_originalHalfSpatialAction
  rw [p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H X]
  unfold p4Q2PZ37I_originalPlaquetteCount
  ring

/-- Exact spatial character-square decomposition of the ORIGINAL
F(2,4) Haar response, including the true linear and constant terms. -/
theorem p4Q2PZ37I_originalF24_traceSquare_decomposition
    (B : Cfg) :
    F 2 4 B = (1/4 : ℝ)*K4 B + NP*F 1 4 B -
      (NP^2/4 : ℝ)*F 0 4 B := by
  have hw : Continuous (fun X : Cfg => w X) :=
    p4Q2PZ36C_half_continuous H
  have hφ : Continuous (fun X : Cfg => Φ X) :=
    p4Q2PW2_originalAllPlaquetteRealTrace_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ36C_cross_continuous H B
  have hA :
      Integrable (fun X : Cfg => (1/4 : ℝ)*(Φ X)^2*(Cross X B)^4) haar :=
    (continuous_const.mul ((hφ.pow 2).mul (hc.pow 4))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB :
      Integrable (fun X : Cfg => NP*(w X*(Cross X B)^4)) haar :=
    (continuous_const.mul (hw.mul (hc.pow 4))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC :
      Integrable (fun X : Cfg => (NP^2/4 : ℝ)*(Cross X B)^4) haar :=
    (continuous_const.mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      (w X)^2*(Cross X B)^4 =
      (1/4 : ℝ)*(Φ X)^2*(Cross X B)^4+
        NP*(w X*(Cross X B)^4)-
        (NP^2/4 : ℝ)*(Cross X B)^4 := by
    rw [p4Q2PZ37I_originalHalfAction_card_sub_trace H X]
    ring
  calc
    F 2 4 B = (∫ X : Cfg, (w X)^2*(Cross X B)^4 ∂haar) := rfl
    _ = ∫ X : Cfg, ((1/4 : ℝ)*(Φ X)^2*(Cross X B)^4+
        NP*(w X*(Cross X B)^4)-
        (NP^2/4 : ℝ)*(Cross X B)^4) ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = (∫ X : Cfg, (1/4 : ℝ)*(Φ X)^2*(Cross X B)^4 ∂haar) +
        (∫ X : Cfg, NP*(w X*(Cross X B)^4) ∂haar) -
        (∫ X : Cfg, (NP^2/4 : ℝ)*(Cross X B)^4 ∂haar) := by
      have hAdd := integral_add hA hB
      have hSub := integral_sub (hA.add hB) hC
      simp only [Pi.add_apply, Pi.sub_apply] at hAdd hSub
      rw [hSub, hAdd]
    _ = (1/4 : ℝ)*K4 B + NP*F 1 4 B - (NP^2/4 : ℝ)*F 0 4 B := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
      simp only [p4Q2PZ37I_originalQuadraticTraceFourth,
        p4Q2PZ37D_originalMixedHaar, pow_zero, one_mul, pow_one]

/-- Unweighted true crossing fourth Haar moment is boundary-independent,
by genuine coordinatewise SU(2) Haar translation. -/
theorem p4Q2PZ37I_originalF04_invariant (B : Cfg) :
    F 0 4 B = F 0 4 I := by
  simpa only [p4Q2PZ37D_originalMixedHaar, pow_zero, one_mul] using
    (p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 4 B)

/-- The full sixth-order mixed source F(2,4) differs from the quadratic
trace source by ONLY an affine function of the true spatial Wilson w. -/
theorem p4Q2PZ37I_originalF24_boundaryDifference_quadratic
    (A B : Cfg) :
    F 2 4 B-F 2 4 A =
      (1/4 : ℝ)*(K4 B-K4 A) +
        (3/32 : ℝ)*NP*(w B-w A) := by
  have h14 (D : Cfg) :
      F 1 4 D = F 1 4 I + (3/32 : ℝ)*w D := by
    simpa only [p4Q2PZ37D_originalMixedHaar,
      p4Q2PZ22_originalSpatialCrossingFourthHaar, pow_one] using
      (p4Q2PZ36_originalF14_affine H D)
  rw [p4Q2PZ37I_originalF24_traceSquare_decomposition H B,
    p4Q2PZ37I_originalF24_traceSquare_decomposition H A,
    h14 B, h14 A,
    p4Q2PZ37I_originalF04_invariant H B,
    p4Q2PZ37I_originalF04_invariant H A]
  ring

/-- Only the genuine plaquette-PAIR fourth-crossing Haar response remains
in the alternating determinant, with factor exactly 1/4. -/
theorem p4Q2PZ37I_originalF24_wedge_quadraticTrace
    (A B C : Cfg) :
    W w (F 2 4) A B C = (1/4 : ℝ)*W w K4 A B C := by
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37I_originalF24_boundaryDifference_quadratic H A B,
    p4Q2PZ37I_originalF24_boundaryDifference_quadratic H A C]
  ring

/-- The original physical seventh six-moment JET coefficient, with its
precise remaining genuine spatial-plaquette-PAIR Haar obstruction.
No O(beta^8) analytic remainder, sign, rank or mass gap is implied. -/
theorem p4Q2PZ37I_originalPhysicalSeventhJet_pairTraceFourth
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w K4 A B C/64 := by
  rw [p4Q2PZ37H_originalPhysicalSeventhJet_oneObstruction H A B C,
    p4Q2PZ37I_originalF24_wedge_quadraticTrace H A B C]
  ring

/-- Symmetry of the two true plaquette insertions, with the full
original crossing fourth power and original spatial Haar untouched. -/
theorem p4Q2PZ37I_originalPairTraceFourth_symm
    (p q : Plaq) (B : Cfg) :
    Pair4 p q B = Pair4 q p B := by
  unfold p4Q2PZ37I_originalPairTraceFourth
  apply integral_congr_ae
  filter_upwards with X
  ring

/-- Expand the quadratic trace moment into ALL ordered pairs of genuine
original SU(2) spatial plaquettes, including diagonal and H=0 cases. -/
theorem p4Q2PZ37I_originalQuadraticTraceFourth_pairSum
    (B : Cfg) :
    K4 B = ∑ p : Plaq, ∑ q : Plaq, Pair4 p q B := by
  classical
  have hχ (p : Plaq) :
      Continuous (fun X : Cfg => χ p X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ36C_cross_continuous H B
  have hEach (p q : Plaq) :
      Integrable (fun X : Cfg => (χ p X*χ q X)*(Cross X B)^4) haar :=
    (((hχ p).mul (hχ q)).mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (p : Plaq) :
      Continuous (fun X : Cfg =>
        ∑ q : Plaq, (χ p X*χ q X)*(Cross X B)^4) := by
    apply continuous_finset_sum
    intro q _hq
    exact ((hχ p).mul (hχ q)).mul (hc.pow 4)
  have hPoint (X : Cfg) :
      (Φ X)^2*(Cross X B)^4 =
      ∑ p : Plaq, ∑ q : Plaq,
        (χ p X*χ q X)*(Cross X B)^4 := by
    have hSquare :
        (∑ p : Plaq, χ p X)*(∑ q : Plaq, χ q X) =
          ∑ p : Plaq, ∑ q : Plaq, χ p X*χ q X := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    calc
      (Φ X)^2*(Cross X B)^4 =
          ((∑ p : Plaq, χ p X)*(∑ q : Plaq, χ q X))*(Cross X B)^4 := by
            unfold p4Q2PW2_originalAllPlaquetteRealTrace
            ring
      _ = (∑ p : Plaq, ∑ q : Plaq, χ p X*χ q X)*(Cross X B)^4 := by
        rw [hSquare]
      _ = ∑ p : Plaq, ∑ q : Plaq,
          (χ p X*χ q X)*(Cross X B)^4 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.sum_mul]
  calc
    K4 B = (∫ X : Cfg, (Φ X)^2*(Cross X B)^4 ∂haar) := rfl
    _ = (∫ X : Cfg, ∑ p : Plaq, ∑ q : Plaq,
          (χ p X*χ q X)*(Cross X B)^4 ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = ∑ p : Plaq, ∑ q : Plaq,
        (∫ X : Cfg, (χ p X*χ q X)*(Cross X B)^4 ∂haar) := by
      rw [integral_finset_sum (Finset.univ : Finset Plaq)
        (fun p _hp =>
          (hInner p).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [integral_finset_sum (Finset.univ : Finset Plaq)
        (fun q _hq => hEach p q)]
    _ = ∑ p : Plaq, ∑ q : Plaq, Pair4 p q B := rfl

end OriginalQuadraticFourth
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalHalfAction_card_sub_trace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalF24_traceSquare_decomposition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalF04_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalF24_boundaryDifference_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalF24_wedge_quadraticTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPhysicalSeventhJet_pairTraceFourth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairTraceFourth_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalQuadraticTraceFourth_pairSum
