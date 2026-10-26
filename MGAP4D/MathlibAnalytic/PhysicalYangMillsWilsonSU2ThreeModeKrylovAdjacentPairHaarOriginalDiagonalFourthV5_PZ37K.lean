import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSquareSchurV5_PZ37K
import Mathlib.Tactic

/-!
# PZ37K — original diagonal fourth-crossing Haar boundary invariance

For a quadruple missing a physical plaquette edge, the true square Schur
projector removes the spatial character square with factor 1/4. Otherwise
PZ33 proves that its four crossing links are distinct. The actual centre
flip then removes each singly occurring Wilson energy against any
centre-even weight. This covers all repeated links and the minimal period.
The seventh-jet result uses only proven diagonal boundary invariance;
minimal-period off-diagonal amplitudes and the actual O(beta^8) remainder
remain separate open obligations.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance (H : ℕ) : IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalDiagonalFourth
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H
local notation "Term4" => p4Q2PZ37I_originalPairFourthTerm H
local notation "Diag4" => p4Q2PZ37J_originalDiagonalFourth H
local notation "Overlap4" => p4Q2PZ37J_originalOverlapFourth H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "I" => (fun _ : Link => (1 : G))

/-- A literal finite list of original temporal Wilson energies. -/
noncomputable def p4Q2PZ37K_originalEnergyProduct
    (ls : List Link) (X B : Cfg) : ℝ :=
  (ls.map (fun e => E ((X e)⁻¹*B e))).prod
local notation "P" => p4Q2PZ37K_originalEnergyProduct H

private theorem product_continuous (ls : List Link) (B : Cfg) :
    Continuous (fun X : Cfg => P ls X B) := by
  induction ls with
  | nil => simpa [p4Q2PZ37K_originalEnergyProduct] using (continuous_const : Continuous (fun _ : Cfg => (1 : ℝ)))
  | cons e ls ih =>
    have he : Continuous (fun X : Cfg => E ((X e)⁻¹*B e)) :=
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        ((continuous_apply e).inv.mul continuous_const)
    simpa [p4Q2PZ37K_originalEnergyProduct] using he.mul ih

private theorem product_translate_free (ls : List Link) (target : Link)
    (h : target ∉ ls) (a : G) (X B : Cfg) :
    P ls (T target a X) B = P ls X B := by
  induction ls with
  | nil => rfl
  | cons e ls ih =>
    have he : e ≠ target := by intro he; apply h; simp [he]
    have ht : target ∉ ls := by intro ht; apply h; exact List.mem_cons_of_mem e ht
    simp only [p4Q2PZ37K_originalEnergyProduct, List.map_cons, List.prod_cons]
    rw [p4Q2PZ35D6_originalLinkTranslate_other H target e a he X]
    exact congrArg (fun r : ℝ => E ((X e)⁻¹*B e)*r) (ih ht)

private theorem product_flip_free (ls : List Link) (target : Link)
    (h : target ∉ ls) (X B : Cfg) : P ls (Flip target X) B = P ls X B := by
  induction ls with
  | nil => rfl
  | cons e ls ih =>
    have he : e ≠ target := by intro he; apply h; simp [he]
    have ht : target ∉ ls := by intro ht; apply h; exact List.mem_cons_of_mem e ht
    simp only [p4Q2PZ37K_originalEnergyProduct, List.map_cons, List.prod_cons]
    rw [p4Q2PU_originalSingleLinkCenterFlip_other H target e he X]
    exact congrArg (fun r : ℝ => E ((X e)⁻¹*B e)*r) (ih ht)

/-- True centre symmetry removes a single temporal energy against an
arbitrary continuous weight even under that same actual link flip. -/
theorem p4Q2PZ37K_originalCenterEven_energy_mean
    (e : Link) (F : Cfg → ℝ) (hF : Continuous F)
    (hEven : ∀ X, F (Flip e X) = F X) (B : Cfg) :
    (∫ X : Cfg, F X*E ((X e)⁻¹*B e) ∂haar) = ∫ X : Cfg, F X ∂haar := by
  let obs : Cfg → ℝ := fun X => F X*(1-E ((X e)⁻¹*B e))
  have hE : Continuous (fun X : Cfg => E ((X e)⁻¹*B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hObs : Continuous obs := hF.mul (continuous_const.sub hE)
  have hOdd (X : Cfg) : obs (Flip e X) = -obs X := by
    dsimp [obs]
    rw [hEven X, p4Q2PY7_originalTemporalLinkTrace_centerOdd H e X B]
    ring
  have hZero := p4Q2PU_originalCenterFlip_Haar_odd_integral_zero H e obs hObs hOdd
  have hiF := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiFE := (hF.mul hE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInt : (∫ X : Cfg, obs X ∂haar) =
      (∫ X : Cfg, F X ∂haar) - (∫ X : Cfg, F X*E ((X e)⁻¹*B e) ∂haar) := by
    calc
      _ = ∫ X : Cfg, F X-F X*E ((X e)⁻¹*B e) ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        dsimp [obs]
        ring
      _ = _ := integral_sub hiF hiFE
  rw [hInt] at hZero
  linarith

/-- Every list of DISTINCT original temporal energies has mean one against
any actual weight even in every link. This is a proved Haar identity. -/
theorem p4Q2PZ37K_originalCenterEven_distinctProduct_mean
    (ls : List Link) (hls : ls.Nodup) (F : Cfg → ℝ) (hF : Continuous F)
    (hEven : ∀ e X, F (Flip e X) = F X) (B : Cfg) :
    (∫ X : Cfg, F X*P ls X B ∂haar) = ∫ X : Cfg, F X ∂haar := by
  induction ls with
  | nil => simp [p4Q2PZ37K_originalEnergyProduct]
  | cons e ls ih =>
    obtain ⟨he, ht⟩ := List.nodup_cons.mp hls
    have hTail : Continuous (fun X : Cfg => F X*P ls X B) :=
      hF.mul (product_continuous H ls B)
    have hTailEven (X : Cfg) : F (Flip e X)*P ls (Flip e X) B = F X*P ls X B := by
      rw [hEven e X, product_flip_free H ls e he X B]
    have h := p4Q2PZ37K_originalCenterEven_energy_mean H e
      (fun X => F X*P ls X B) hTail hTailEven B
    calc
      _ = ∫ X : Cfg, (F X*P ls X B)*E ((X e)⁻¹*B e) ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        simp only [p4Q2PZ37K_originalEnergyProduct, List.map_cons, List.prod_cons]
        ring
      _ = ∫ X : Cfg, F X*P ls X B ∂haar := h
      _ = _ := ih ht

/-- The genuine original normalized plaquette-character square has Haar
mean 1/4 at EVERY finite period, derived from one actual free edge. -/
theorem p4Q2PZ37K_originalPlaquetteSquare_mean (p : Plaq) :
    (∫ X : Cfg, (χ p X)^2 ∂haar) = (1/4 : ℝ) := by
  have h := p4Q2PZ37K_originalPlaquetteSquare_freeEdgeProject H p
    (p4Q2PU3_originalPlaquetteEdge0 H p) (Or.inl rfl)
    (fun _ => 1) continuous_const (by intros; rfl)
  simpa using h

/-- No assumptions about repeated links: each genuine diagonal term
is exactly one quarter its unweighted temporal-product Haar integral. -/
theorem p4Q2PZ37K_originalDiagonalFourthTerm_decouple
    (p : Plaq) (e f g k : Link) (B : Cfg) :
    Term4 p p e f g k B = (1/4 : ℝ) *
      (∫ X : Cfg, P [e,f,g,k] X B ∂haar) := by
  classical
  have hForm : Term4 p p e f g k B =
      ∫ X : Cfg, (χ p X)^2*P [e,f,g,k] X B ∂haar := by
    unfold p4Q2PZ37I_originalPairFourthTerm
    apply integral_congr_ae
    filter_upwards with X
    simp only [p4Q2PZ37K_originalEnergyProduct, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rw [hForm]
  by_cases hCover : p4Q2PZ25_originalFourthCrossingCoversPlaquette H p e f g k
  · have hNodup := p4Q2PZ33_originalCover_crossings_nodup H p e f g k hCover
    rw [p4Q2PZ37K_originalCenterEven_distinctProduct_mean H [e,f,g,k] hNodup
      (fun X => (χ p X)^2) ((p4Q2PV_originalPlaquetteRealCharacter_continuous H p).pow 2)
      (fun t X => p4Q2PY7_originalPlaquetteCharSquare_centerEven H p t X) B,
      p4Q2PZ37K_originalPlaquetteSquare_mean H p]
    have hBare := p4Q2PZ37K_originalCenterEven_distinctProduct_mean H [e,f,g,k] hNodup
      (fun _ => 1) continuous_const (by intros; rfl) B
    have hOne : (∫ X : Cfg, P [e,f,g,k] X B ∂haar) = 1 := by simpa using hBare
    rw [hOne, mul_one]
  · have hMissing : ∃ target : Link,
        (target = p4Q2PU3_originalPlaquetteEdge0 H p ∨
         target = p4Q2PU3_originalPlaquetteEdge1 H p ∨
         target = p4Q2PU3_originalPlaquetteEdge2 H p ∨
         target = p4Q2PU3_originalPlaquetteEdge3 H p) ∧ target ∉ [e,f,g,k] := by
      by_contra hNo
      apply hCover
      intro target hEdge
      have hm : target ∈ [e,f,g,k] := by
        by_contra hm
        exact hNo ⟨target,hEdge,hm⟩
      simpa using hm
    obtain ⟨target,hEdge,hFree⟩ := hMissing
    exact p4Q2PZ37K_originalPlaquetteSquare_freeEdgeProject H p target hEdge
      (fun X => P [e,f,g,k] X B) (product_continuous H _ B)
      (fun a X => product_translate_free H _ target hFree a X B)

/-- Genuine full product-Haar translation removes the entire original
right boundary from a temporal product, including repeated links. -/
theorem p4Q2PZ37K_originalEnergyProduct_boundaryInvariant (ls : List Link) (B : Cfg) :
    (∫ X : Cfg, P ls X B ∂haar) = ∫ X : Cfg, P ls X I ∂haar := by
  let Tfull : Cfg → Cfg := fun X e => B e*X e
  have hT : MeasurePreserving Tfull haar haar :=
    p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving H B
  calc
    _ = ∫ X : Cfg, P ls (Tfull X) B ∂haar :=
      p4Q2PZ37H_originalHaar_change H Tfull hT _ (product_continuous H ls B)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with X
      unfold p4Q2PZ37K_originalEnergyProduct
      congr 1
      apply List.map_congr_left
      intro e _
      dsimp [Tfull]
      congr 1
      group

/-- All true diagonal fourth terms are boundary-invariant. -/
theorem p4Q2PZ37K_originalDiagonalFourthTerm_boundaryInvariant
    (p : Plaq) (e f g k : Link) (B : Cfg) :
    Term4 p p e f g k B = Term4 p p e f g k I := by
  rw [p4Q2PZ37K_originalDiagonalFourthTerm_decouple H p e f g k B,
    p4Q2PZ37K_originalDiagonalFourthTerm_decouple H p e f g k I,
    p4Q2PZ37K_originalEnergyProduct_boundaryInvariant H [e,f,g,k] B]

/-- The original fourfold expansion includes ALL repeated crossing links.
Each diagonal plaquette response is boundary-invariant at every H. -/
theorem p4Q2PZ37K_originalDiagonalPairFourth_boundaryInvariant (p : Plaq) (B : Cfg) :
    Pair4 p p B = Pair4 p p I := by
  classical
  rw [p4Q2PZ37I_originalPairFourth_quadrupleExpansion H p p B,
    p4Q2PZ37I_originalPairFourth_quadrupleExpansion H p p I]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro k _
  exact p4Q2PZ37K_originalDiagonalFourthTerm_boundaryInvariant H p e f g k B

/-- D_H is an actual boundary constant, now proved from original Haar. -/
theorem p4Q2PZ37K_originalDiagonalFourth_boundaryInvariant (B : Cfg) :
    Diag4 B = Diag4 I := by
  unfold p4Q2PZ37J_originalDiagonalFourth
  apply Finset.sum_congr rfl
  intro p _
  exact p4Q2PZ37K_originalDiagonalPairFourth_boundaryInvariant H p B

/-- The alternating diagonal wedge vanishes for all three boundaries and H. -/
theorem p4Q2PZ37K_originalDiagonalFourth_wedge_zero (A B C : Cfg) :
    W w Diag4 A B C = 0 := by
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37K_originalDiagonalFourth_boundaryInvariant H A,
    p4Q2PZ37K_originalDiagonalFourth_boundaryInvariant H B,
    p4Q2PZ37K_originalDiagonalFourth_boundaryInvariant H C]
  ring

/-- All-period physical seventh Taylor JET: only the genuine exceptional
off-diagonal pair response remains; no minimal-overlap amplitude is removed. -/
theorem p4Q2PZ37K_originalPhysicalSeventhJet_overlapOnly (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w Overlap4 A B C/64 := by
  rw [p4Q2PZ37J_originalPhysicalSeventhJet_diagonal_overlap H A B C,
    p4Q2PZ37K_originalDiagonalFourth_wedge_zero H A B C]
  ring

/-- Unconditional nonminimal-period pure Vandermonde seventh Taylor JET.
This does not assert an eighth-order remainder for the actual Wilson minor. -/
theorem p4Q2PZ37K_originalPhysicalSeventhJet_nonminimal_vandermonde
    (hH : 1 ≤ H) (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 := by
  rw [p4Q2PZ37J_originalPhysicalSeventhJet_nonminimal_diagonal H hH A B C,
    p4Q2PZ37K_originalDiagonalFourth_wedge_zero H A B C]
  ring

end OriginalDiagonalFourth
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalCenterEven_energy_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalCenterEven_distinctProduct_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalPlaquetteSquare_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalDiagonalFourthTerm_decouple
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalEnergyProduct_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalDiagonalFourthTerm_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalDiagonalPairFourth_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalDiagonalFourth_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalDiagonalFourth_wedge_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalPhysicalSeventhJet_overlapOnly
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalPhysicalSeventhJet_nonminimal_vandermonde
