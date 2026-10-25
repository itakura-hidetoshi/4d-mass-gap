import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourEdgePermutationV5_PZ33
import Mathlib.Tactic

/-!
# P4-Q2-PZ34 — the genuine SU(2) fourth Haar survivor has EXACT 4! multiplicity

The PZ33 original center-flip and physical-plaquette geometry constrain all
surviving ordered temporal Wilson crossing link quadruples to permutations
of the four distinct original plaquette edges, including H=0.

PZ34 now uses ONLY the ordinary real commutativity of four original
Wilson crossing energies to prove the genuine Haar integrands agree
for all those permutations. A finite combinatorial bijection to
List.permutations of the original four-link list, with the exact
List.length_permutations and no-duplicates theorems from mathlib,
shows that the support contains 4!=24 different ordered quadruples.
It follows that S4 is 24 times ONE genuinely ordered Haar integral per
original physical plaquette. Thus D14 and the sixth Ward residual
become exact 12 and 360 multiples, respectively.

No SU(2) Haar fourth-moment coefficient, D14 affine law, nonzero
sixth Ward, rank3, Hankel positivity or continuum mass gap is claimed.
No new axiom, sorry, admit, native_decide or independent posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ34_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ34_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalFourEdgeFactorial
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Quad" => (Link × (Link × (Link × Link)))
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "Term4" => p4Q2PZ25_originalFourCrossingPlaquetteTerm H
local notation "Permuted4" => p4Q2PZ33_originalPermutedPlaquetteFourthHaar H
local notation "S4" => p4Q2PZ32_originalCoveredFourthSupportSum H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "D14" => p4Q2PZ24_originalCenteredFirstFourthDefect H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H
local notation "Low6" => p4Q2PZ32_originalSixthWardLowBaseline H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

private def p4Q2PZ34_baseList (p : Plaq) : List Link :=
  [e0 p, e1 p, e2 p, e3 p]

private def p4Q2PZ34_quadList (q : Quad) : List Link :=
  [q.1, q.2.1, q.2.2.1, q.2.2.2]

/-- True center-selected quadruples represented as a finite set of
ordered real spatial links, not a replacement physical lattice. -/
noncomputable def p4Q2PZ34_originalPermutationSupport (p : Plaq) :
    Finset Quad := by
  classical
  exact Finset.univ.filter (fun q =>
    (p4Q2PZ34_quadList H q).Perm (p4Q2PZ34_baseList H p))

private theorem p4Q2PZ34_quadList_injective :
    Function.Injective (p4Q2PZ34_quadList H) := by
  intro q r h
  rcases q with ⟨a,b,c,d⟩
  rcases r with ⟨a',b',c',d'⟩
  simp only [p4Q2PZ34_quadList, List.cons.injEq, and_true] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem p4Q2PZ34_four_of_perm
    (p : Plaq) {l : List Link}
    (hp : l.Perm (p4Q2PZ34_baseList H p)) :
    ∃ a b c d : Link, l = [a,b,c,d] := by
  have hlen : l.length = 4 := by
    simpa [p4Q2PZ34_baseList] using hp.length_eq
  cases l with
  | nil => simp at hlen
  | cons a t =>
      cases t with
      | nil => simp at hlen
      | cons b t =>
          cases t with
          | nil => simp at hlen
          | cons c t =>
              cases t with
              | nil => simp at hlen
              | cons d t =>
                  cases t with
                  | nil => exact ⟨a,b,c,d,rfl⟩
                  | cons x t => simp at hlen

/-- Genuine four-crossing support is bijective, through its ordered
link list, to ALL permutations of the original four-edge list. -/
theorem p4Q2PZ34_originalSupport_image_eq_permutations (p : Plaq) :
    (p4Q2PZ34_originalPermutationSupport H p).image
        (p4Q2PZ34_quadList H) =
      (p4Q2PZ34_baseList H p).permutations.toFinset := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
    have hp : (p4Q2PZ34_quadList H q).Perm
        (p4Q2PZ34_baseList H p) := by
      simpa [p4Q2PZ34_originalPermutationSupport] using hq
    simpa only [List.mem_toFinset, List.mem_permutations] using hp
  · intro hl
    have hp : l.Perm (p4Q2PZ34_baseList H p) := by
      simpa only [List.mem_toFinset, List.mem_permutations] using hl
    obtain ⟨a,b,c,d,rfl⟩ := p4Q2PZ34_four_of_perm H p hp
    apply Finset.mem_image.mpr
    refine ⟨(a,(b,(c,d))), ?_, rfl⟩
    simpa [p4Q2PZ34_originalPermutationSupport,
      p4Q2PZ34_quadList] using hp

/-- The true four-edge-covering temporal link support has EXACTLY
24 ordered configurations for every original plaquette and every
finite even periodic lattice, including physical side two. -/
theorem p4Q2PZ34_originalSupport_card_twentyFour (p : Plaq) :
    (p4Q2PZ34_originalPermutationSupport H p).card = 24 := by
  classical
  let s := p4Q2PZ34_originalPermutationSupport H p
  have hi : (s.image (p4Q2PZ34_quadList H)).card = s.card :=
    Finset.card_image_of_injective s (p4Q2PZ34_quadList_injective H)
  have hn : (p4Q2PZ34_baseList H p).Nodup := by
    simpa only [p4Q2PZ34_baseList] using
      (p4Q2PZ33_originalFourEdges_list_nodup H p)
  calc
    s.card = (s.image (p4Q2PZ34_quadList H)).card := hi.symm
    _ = (p4Q2PZ34_baseList H p).permutations.toFinset.card := by
      rw [p4Q2PZ34_originalSupport_image_eq_permutations H p]
    _ = (p4Q2PZ34_baseList H p).permutations.length :=
      List.toFinset_card_of_nodup
        (List.nodup_permutations (p4Q2PZ34_baseList H p) hn)
    _ = 24 := by
      rw [List.length_permutations]
      norm_num [p4Q2PZ34_baseList]

/-- The ORIGINAL SU(2) Haar integrand has a real commutative
four-crossing energy product: permuting the four original spatial
link indices does NOT change its integral or physical Wilson action. -/
theorem p4Q2PZ34_originalFourCrossingTerm_perm
    (p : Plaq) (e f g k : Link) (B : Cfg)
    (hp : ([e,f,g,k] : List Link).Perm [e0 p,e1 p,e2 p,e3 p]) :
    Term4 p e f g k B = Term4 p (e0 p) (e1 p) (e2 p) (e3 p) B := by
  have hprod (A : Cfg) :
      E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g) * E ((A k)⁻¹ * B k) =
        E ((A (e0 p))⁻¹ * B (e0 p)) *
          E ((A (e1 p))⁻¹ * B (e1 p)) *
          E ((A (e2 p))⁻¹ * B (e2 p)) *
          E ((A (e3 p))⁻¹ * B (e3 p)) := by
    let energy : Link → ℝ := fun d => E ((A d)⁻¹ * B d)
    have h := (hp.map energy).prod_eq
    simpa only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using h
  unfold p4Q2PZ25_originalFourCrossingPlaquetteTerm
  apply integral_congr_ae
  filter_upwards with A
  exact congrArg (fun u : ℝ => χ p A * u) (hprod A)

/-- A single original Wilson spatial plaquette contributes one
standard ordered genuine Haar integral. No group integration
evaluation has been performed. -/
noncomputable def p4Q2PZ34_originalCanonicalFourCrossingHaar
    (p : Plaq) (B : Cfg) : ℝ :=
  Term4 p (e0 p) (e1 p) (e2 p) (e3 p) B

/-- Rewrite the PZ33 genuine permutation sum exactly as the sum
over the finite support of original ordered four-link tuples. -/
theorem p4Q2PZ34_originalPermutationHaar_eq_supportSum
    (p : Plaq) (B : Cfg) :
    Permuted4 p B =
      ∑ q ∈ p4Q2PZ34_originalPermutationSupport H p,
        Term4 p q.1 q.2.1 q.2.2.1 q.2.2.2 B := by
  classical
  unfold p4Q2PZ33_originalPermutedPlaquetteFourthHaar
    p4Q2PZ34_originalPermutationSupport
  simp only [Finset.sum_filter, Fintype.sum_prod_type,
    p4Q2PZ34_quadList, p4Q2PZ34_baseList]

/-- Exact factorial multiplicity: all 24 actual original
SU(2) four-crossing Haar integrals equal the canonical term. -/
theorem p4Q2PZ34_originalPermutedFourth_eq_twentyFour
    (p : Plaq) (B : Cfg) :
    Permuted4 p B = 24 * p4Q2PZ34_originalCanonicalFourCrossingHaar H p B := by
  classical
  rw [p4Q2PZ34_originalPermutationHaar_eq_supportSum H p B]
  calc
    (∑ q ∈ p4Q2PZ34_originalPermutationSupport H p,
      Term4 p q.1 q.2.1 q.2.2.1 q.2.2.2 B) =
      ∑ _q ∈ p4Q2PZ34_originalPermutationSupport H p,
        p4Q2PZ34_originalCanonicalFourCrossingHaar H p B := by
          apply Finset.sum_congr rfl
          intro q hq
          have hp : (p4Q2PZ34_quadList H q).Perm
              (p4Q2PZ34_baseList H p) := by
            simpa [p4Q2PZ34_originalPermutationSupport] using hq
          rcases q with ⟨a,b,c,d⟩
          exact p4Q2PZ34_originalFourCrossingTerm_perm
            H p a b c d B (by simpa [p4Q2PZ34_quadList,
              p4Q2PZ34_baseList] using hp)
    _ = (p4Q2PZ34_originalPermutationSupport H p).card *
        p4Q2PZ34_originalCanonicalFourCrossingHaar H p B := by
          simp [nsmul_eq_mul]
    _ = 24 * p4Q2PZ34_originalCanonicalFourCrossingHaar H p B := by
          rw [p4Q2PZ34_originalSupport_card_twentyFour H p]
          norm_num

/-- PZ32's COMPLETE remaining true fourth-spatial Haar support
is 24 times one standard genuinely ordered SU(2) Haar integral
for each ORIGINAL spatial plaquette. -/
theorem p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar (B : Cfg) :
    S4 B = 24 * ∑ p : Plaq,
      p4Q2PZ34_originalCanonicalFourCrossingHaar H p B := by
  classical
  rw [p4Q2PZ33_originalS4_eq_allPermutationHaar H B]
  unfold p4Q2PZ33_originalAllPlaquettePermutationHaar
  simp_rw [p4Q2PZ34_originalPermutedFourth_eq_twentyFour H]
  rw [Finset.mul_sum]

/-- The remaining physical boundary-normalized original D14
becomes exactly 12 times a difference of original Haar rows. -/
theorem p4Q2PZ34_originalD14_eq_twelveCanonicalHaarDifference
    (B : Cfg) :
    D14 B = 12 * (
      (∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p B) -
      (∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p I)) := by
  rw [p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference H B,
    p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H B,
    p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H I]
  ring

/-- The original physical sixth Ward obstruction is now the genuine
low-sector Ward term minus 360 times a determinant of true SU(2)
four-edge Haar moments; its nonzero value remains OPEN. -/
theorem p4Q2PZ34_originalSixthWard_canonicalFourHaar
    (A B C : Cfg) :
    W6 A B C = Low6 A B C -
      360 * (
        (w B - w A) *
          ((∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p C) -
            (∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p A)) -
        (w C - w A) *
          ((∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p B) -
            (∑ p : Plaq, p4Q2PZ34_originalCanonicalFourCrossingHaar H p A))) := by
  rw [p4Q2PZ32_originalSixthWard_onlyCoveredFourthSupport H A B C,
    p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H A,
    p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H B,
    p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H C]
  ring

end OriginalFourEdgeFactorial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalSupport_image_eq_permutations
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalSupport_card_twentyFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalFourCrossingTerm_perm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalPermutationHaar_eq_supportSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalPermutedFourth_eq_twentyFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalD14_eq_twelveCanonicalHaarDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ34_originalSixthWard_canonicalFourHaar
