import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSharedLinkSchurV5_PZ37L
import Mathlib.Tactic

/-!
# PZ37L — exact six-link overlap amplitude in the original spatial Haar

Two genuinely shared coordinates are contracted before the four odd-edge
Wilson energies. The result is 1/1024 times two original boundary loop
characters. This theorem keeps arbitrary genuine link indices and proves
the necessary distinctness obligations explicitly through a six-link Nodup.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "ch" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance (H : ℕ) : IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
namespace GroundStatePosteriorJoint
section SixLink
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H

private theorem ch_cont : Continuous ch :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- Two original shared edges separate the pair into two winding characters. -/
theorem p4Q2PZ37L_originalSpatialHaar_twoSharedProject
    (a b c d s t : Link) (hn : ([a,b,c,d,s,t] : List Link).Nodup)
    (F : Cfg → ℝ) (hF : Continuous F)
    (hs : ∀ u X, F (T s u X) = F X)
    (ht : ∀ u X, F (T t u X) = F X) :
    (∫ X : Cfg,
      ch (X a*X s*(X b)⁻¹*(X t)⁻¹)*
      ch (X c*X t*(X d)⁻¹*(X s)⁻¹)*F X ∂haar) =
      (1/4 : ℝ)*(∫ X : Cfg, ch (X a*X c)*ch (X b*X d)*F X ∂haar) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hn
  have hPair := p4Q2PZ37L_originalSpatialHaar_pairProject H s
    (fun X => (X b)⁻¹*(X t)⁻¹*X a) (fun X => X c*X t*(X d)⁻¹) F
    (by fun_prop) (by fun_prop) hF
    (by intro u X; simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show b ≠ s by tauto, show t ≠ s by tauto, show a ≠ s by tauto])
    (by intro u X; simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show c ≠ s by tauto, show t ≠ s by tauto, show d ≠ s by tauto]) hs
  have hConj := p4Q2PZ37L_originalSpatialHaar_conjugationProject H t
    (fun X => X a*X c) (fun X => (X d)⁻¹*(X b)⁻¹) F
    (by fun_prop) (by fun_prop) hF
    (by intro u X; simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show a ≠ t by tauto, show c ≠ t by tauto])
    (by intro u X; simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show d ≠ t by tauto, show b ≠ t by tauto]) ht
  calc
    _ = ∫ X : Cfg,
        ch (X s*((X b)⁻¹*(X t)⁻¹*X a))*
        ch ((X s)⁻¹*(X c*X t*(X d)⁻¹))*F X ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      have hp := p4Q2PZ35D5_originalCharacter_mul_comm
        (X a) (X s*(X b)⁻¹*(X t)⁻¹)
      have hq := p4Q2PZ35D5_originalCharacter_mul_comm
        (X c*X t*(X d)⁻¹) (X s)⁻¹
      simp only [mul_assoc] at hp hq ⊢
      rw [hp, hq]
    _ = (1/4 : ℝ)*(∫ X : Cfg,
        ch ((X c*X t*(X d)⁻¹)*((X b)⁻¹*(X t)⁻¹*X a))*F X ∂haar) := hPair
    _ = (1/4 : ℝ)*(∫ X : Cfg,
        ch ((X t)⁻¹*(X a*X c)*X t*((X d)⁻¹*(X b)⁻¹))*F X ∂haar) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with X
      have hh := p4Q2PZ35D5_originalCharacter_mul_comm
        (X c*X t*(X d)⁻¹*(X b)⁻¹) ((X t)⁻¹*X a)
      simpa only [mul_assoc] using congrArg (fun r : ℝ => r*F X) hh
    _ = (1/4 : ℝ)*(∫ X : Cfg,
        ch (X a*X c)*ch ((X d)⁻¹*(X b)⁻¹)*F X ∂haar) := congrArg _ hConj
    _ = _ := by simp_rw [← mul_inv_rev, p4Q2PZ35D5_originalCharacter_inv]

/-- A genuine two-link winding character with its two Wilson insertions. -/
theorem p4Q2PZ37L_originalSpatialHaar_twoCycleProject
    (a c : Link) (hac : a ≠ c) (B : Cfg) (F : Cfg → ℝ) (hF : Continuous F)
    (ha : ∀ u X, F (T a u X) = F X)
    (hc : ∀ u X, F (T c u X) = F X) :
    (∫ X : Cfg, ch (X a*X c)*E ((X a)⁻¹*B a)*E ((X c)⁻¹*B c)*F X ∂haar) =
      (1/16 : ℝ)*ch (B a*B c)*(∫ X : Cfg, F X ∂haar) := by
  have hE : Continuous (fun X : Cfg => E ((X c)⁻¹*B c)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply c).inv.mul continuous_const)
  have h1 := p4Q2PZ35D8_originalSpatialHaar_forwardProject H a (B a)
    (fun X => X c) (fun X => E ((X c)⁻¹*B c)*F X)
    (continuous_apply c) (hE.mul hF)
    (by intro u X; exact p4Q2PZ35D6_originalLinkTranslate_other H a c u hac.symm X)
    (by intro u X; dsimp only
        rw [p4Q2PZ35D6_originalLinkTranslate_other H a c u hac.symm X, ha])
  have h2 := p4Q2PZ35D8_originalSpatialHaar_forwardProject H c (B c)
    (fun _ => B a) F continuous_const hF (by intros; rfl) hc
  calc
    _ = ∫ X : Cfg,
        (ch (X a*X c)*E ((X a)⁻¹*B a))*(E ((X c)⁻¹*B c)*F X) ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      ring
    _ = -(1/4 : ℝ)*(∫ X : Cfg, ch (B a*X c)*(E ((X c)⁻¹*B c)*F X) ∂haar) := h1
    _ = -(1/4 : ℝ)*(∫ X : Cfg, (ch (X c*B a)*E ((X c)⁻¹*B c))*F X ∂haar) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with X
      rw [p4Q2PZ35D5_originalCharacter_mul_comm (B a) (X c)]
      ring
    _ = -(1/4 : ℝ)*(-(1/4 : ℝ)*(∫ X : Cfg, ch (B c*B a)*F X ∂haar)) := congrArg _ h2
    _ = _ := by
      rw [integral_const_mul, p4Q2PZ35D5_originalCharacter_mul_comm (B c) (B a)]
      ring

/-- Exact six-link original Haar amplitude: all four odd edges inserted once. -/
theorem p4Q2PZ37L_originalSixLinkOverlap_exact
    (a b c d s t : Link) (hn : ([a,b,c,d,s,t] : List Link).Nodup) (B : Cfg) :
    (∫ X : Cfg,
      ch (X a*X s*(X b)⁻¹*(X t)⁻¹)*
      ch (X c*X t*(X d)⁻¹*(X s)⁻¹)*
      (E ((X a)⁻¹*B a)*E ((X b)⁻¹*B b)*E ((X c)⁻¹*B c)*E ((X d)⁻¹*B d)) ∂haar) =
      (1/1024 : ℝ)*ch (B a*B c)*ch (B b*B d) := by
  have hnd := hn
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hnd
  let EAt : Link → Cfg → ℝ := fun e X => E ((X e)⁻¹*B e)
  have hE (e : Link) : Continuous (EAt e) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hp := p4Q2PZ37L_originalSpatialHaar_twoSharedProject H a b c d s t hn
    (fun X => EAt a X*EAt b X*EAt c X*EAt d X)
    ((((hE a).mul (hE b)).mul (hE c)).mul (hE d))
    (by intro u X; simp [EAt, p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show a ≠ s by tauto, show b ≠ s by tauto, show c ≠ s by tauto, show d ≠ s by tauto])
    (by intro u X; simp [EAt, p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show a ≠ t by tauto, show b ≠ t by tauto, show c ≠ t by tauto, show d ≠ t by tauto])
  have h1 := p4Q2PZ37L_originalSpatialHaar_twoCycleProject H a c (by tauto) B
    (fun X => ch (X b*X d)*EAt b X*EAt d X)
    ((((ch_cont).comp ((continuous_apply b).mul (continuous_apply d))).mul (hE b)).mul (hE d))
    (by intro u X; simp [EAt, p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show b ≠ a by tauto, show d ≠ a by tauto])
    (by intro u X; simp [EAt, p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate,
      show b ≠ c by tauto, show d ≠ c by tauto])
  have h2 := p4Q2PZ37L_originalSpatialHaar_twoCycleProject H b d (by tauto) B
    (fun _ => 1) continuous_const (by intros; rfl) (by intros; rfl)
  have h2' : (∫ X : Cfg, ch (X b*X d)*EAt b X*EAt d X ∂haar) =
      (1/16 : ℝ)*ch (B b*B d) := by simpa [EAt] using h2
  calc
    _ = (1/4 : ℝ)*(∫ X : Cfg, ch (X a*X c)*ch (X b*X d)*
        (EAt a X*EAt b X*EAt c X*EAt d X) ∂haar) := hp
    _ = (1/4 : ℝ)*(∫ X : Cfg, ch (X a*X c)*EAt a X*EAt c X*
        (ch (X b*X d)*EAt b X*EAt d X) ∂haar) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with X
      ring
    _ = (1/4 : ℝ)*((1/16 : ℝ)*ch (B a*B c)*
        (∫ X : Cfg, ch (X b*X d)*EAt b X*EAt d X ∂haar)) := congrArg _ h1
    _ = _ := by rw [h2']; ring

end SixLink
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSpatialHaar_twoSharedProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSpatialHaar_twoCycleProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSixLinkOverlap_exact
