import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeOddFilteredRankV5_PZ37ARZ
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ASA — explicit symmetric feature indices and genuine vertex parity

Expose the actual symmetric Taylor factors on the literal links; both
interacting halfweights and all permutation multiplicities are unchanged.
The central SU(2) transformation at a vertex gives the sign (-1)^degree,
counting both endpoints (a loop contributes twice). Odd vertex degree
annihilates a weighted right feature in the actual excitation space.
Even degree is necessary, not sufficient, for a nonzero projection.
No global survivor count or uniform spectral estimate is asserted.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37ASA_two_pos : 0 < (2 : ℕ) := by decide

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "Raw" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
local notation "Kernel" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "L" => periodicHypercubicEvenSpatialSliceLinkList
local notation "NK" => p4Q2PZ37ARA_normalizedKernel
local notation "h2" => p4Q2PZ37ASA_two_pos

local instance p4Q2PZ37ASA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ASA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ASA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ASA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ASA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ASA_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ASA_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ASA_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ASA_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ASA_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00


local notation "Gauge" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation
local notation "GT" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
local notation "Pull" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)


local notation "J" => ((Fin 2 × Fin 2) × Bool)
local notation "Tr" => specialUnitaryNormalizedTraceRelativeKernel
local notation "kp" => specialUnitaryWilsonRelativeKernelPartial
local notation "Vtx" => PeriodicHypercubicEvenSpatialSliceVertex
local notation "Idx" => PZ37ARXLocalIndex
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "c0" => p4Q2PZ35D4_centralMinusOne

private theorem p4Q2PZ37ASA_coord_cont (q : J) :
    Continuous (p4Q2PZ37ARZ_coord q) := by
  have hMat : Continuous (fun g : G => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_subtype_val
  have hEntry : Continuous (fun g : G => (g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2 q.1.1) :=
    (continuous_apply q.1.1).comp ((continuous_apply q.1.2).comp hMat)
  unfold p4Q2PZ37ARZ_coord
  split
  · exact Complex.continuous_re.comp hEntry
  · exact Complex.continuous_im.comp hEntry

private theorem p4Q2PZ37ASA_trace_sum (g h : G) :
    Tr 2 g h = ∑ q : J, (p4Q2PZ37ARZ_coord q g/2)*p4Q2PZ37ARZ_coord q h := by
  rw [specialUnitaryNormalizedTraceRelativeKernel_eq_scaled,
    specialUnitaryRealTraceRelativeKernel_eq_inner, PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [realScalarInner_eq_mul]
  change (1/(2:ℝ))*(p4Q2PZ37ARZ_coord q g*p4Q2PZ37ARZ_coord q h) = _
  ring

private def p4Q2PZ37ASA_left (beta : ℝ) {m : ℕ} (i : PZ37ARXLocalIndex m) (g : G) : ℝ :=
  (Real.exp (-beta)*(beta^i.1.val/(Nat.factorial i.1.val : ℝ))) *
    (i.2.val.countPerms : ℝ) *
    (i.2.val.map (fun q => p4Q2PZ37ARZ_coord q g / 2)).prod

private def p4Q2PZ37ASA_right {m : ℕ} (i : PZ37ARXLocalIndex m) (g : G) : ℝ :=
  (i.2.val.map (fun q => p4Q2PZ37ARZ_coord q g)).prod

private theorem p4Q2PZ37ASA_cont_prod
    {X I : Type} [TopologicalSpace X] (s : Finset I) (f : I → X → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : X => (1:ℝ)))
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hf i).mul ih

private theorem p4Q2PZ37ASA_cont_multiset_prod
    {X I : Type} [TopologicalSpace X] (s : Multiset I) (f : I → X → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => (s.map (fun i => f i x)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : X => (1:ℝ)))
  | cons i s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (hf i).mul ih

private theorem p4Q2PZ37ASA_left_cont (beta : ℝ) {m : ℕ} (i : PZ37ARXLocalIndex m) :
    Continuous (p4Q2PZ37ASA_left beta i) := by
  unfold p4Q2PZ37ASA_left
  exact continuous_const.mul (p4Q2PZ37ASA_cont_multiset_prod i.2.val
    (fun q => fun g : G => p4Q2PZ37ARZ_coord q g / 2)
    (fun q => (p4Q2PZ37ASA_coord_cont q).div_const 2))

private theorem p4Q2PZ37ASA_right_cont {m : ℕ} (i : PZ37ARXLocalIndex m) :
    Continuous (p4Q2PZ37ASA_right i) := by
  unfold p4Q2PZ37ASA_right
  exact p4Q2PZ37ASA_cont_multiset_prod i.2.val _ p4Q2PZ37ASA_coord_cont

private theorem p4Q2PZ37ASA_local_expansion
    (beta : ℝ) (m : ℕ) (g h : G) :
    kp 2 beta m g h = ∑ i : PZ37ARXLocalIndex m,
      p4Q2PZ37ASA_left beta i g*p4Q2PZ37ASA_right i h := by
  classical
  unfold specialUnitaryWilsonRelativeKernelPartial
  rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum,
    ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow,p4Q2PZ37ASA_trace_sum]
  have hp : (∑ q : J, (p4Q2PZ37ARZ_coord q g/2)*p4Q2PZ37ARZ_coord q h)^j.val =
      ∑ p : Sym J j.val, (p.val.countPerms : ℝ) *
        (p.val.map (fun q => (p4Q2PZ37ARZ_coord q g/2)*p4Q2PZ37ARZ_coord q h)).prod := by
    simpa only [Finset.sym_univ] using
      (Finset.sum_pow (s := (Finset.univ : Finset J))
        (fun q => (p4Q2PZ37ARZ_coord q g/2)*p4Q2PZ37ARZ_coord q h) j.val)
  rw [hp]
  calc
    _ = ∑ p : Sym J j.val,
        (Real.exp (-beta)*(beta^j.val/(Nat.factorial j.val : ℝ))) *
          ((p.val.countPerms : ℝ) *
            (p.val.map (fun q => (p4Q2PZ37ARZ_coord q g/2)*p4Q2PZ37ARZ_coord q h)).prod) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Multiset.prod_map_mul]
      unfold p4Q2PZ37ASA_left p4Q2PZ37ASA_right
      ring

/-- Expand and separate a finite product with abstract index types before
specializing to the literal Wilson geometry. -/
private theorem p4Q2PZ37ASA_weighted_product
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (u v : ℝ) (k : ι → ℝ) (a b : ι → κ → ℝ)
    (hk : ∀ l, k l = ∑ i, a l i * b l i) :
    u * (∏ l, k l) * v =
      ∑ i : ι → κ, (u * ∏ l, a l (i l)) * (v * ∏ l, b l (i l)) := by
  classical
  have hkprod : (∏ l, k l) = ∏ l, ∑ i, a l i * b l i :=
    Finset.prod_congr rfl (fun l _ => hk l)
  calc
    _ = u * (∏ l, ∑ i, a l i * b l i) * v := by rw [hkprod]
    _ = u * (∑ i : ι → κ, ∏ l, a l (i l) * b l (i l)) * v := by
      rw [Fintype.prod_sum (fun l i => a l i * b l i)]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.prod_mul_distrib]
      ring


/-- Actual central vertex gauge transformation. -/
def p4Q2PZ37ASA_vertexFlip (H : ℕ) (v : Vtx H) : Gauge H 2 :=
  fun w => if w = v then c0 else 1

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_vertexFlip

/-- Both endpoint incidences, including twice for a loop at v. -/
def p4Q2PZ37ASA_incidence (H : ℕ) (v : Vtx H) (l : Link H) : ℕ :=
  (if l.1 = v then 1 else 0) +
    (if periodicHypercubicEvenSpatialSliceShift H l.1 l.2 = v then 1 else 0)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_incidence

def p4Q2PZ37ASA_vertexDegree (H m : ℕ) (v : Vtx H)
    (j : Link H → Idx m) : ℕ :=
  ∑ l : Link H, p4Q2PZ37ASA_incidence H v l * (j l).1.val

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_vertexDegree

private theorem p4Q2PZ37ASA_center_inv : c0⁻¹ = c0 := by
  have hcc : c0 * c0 = (1 : G) := by
    apply Subtype.ext
    change ((c0 : G) : Mat) * ((c0 : G) : Mat) = (1 : Mat)
    simp [p4Q2PZ35D4_centralMinusOne_coe]
  calc
    c0⁻¹ = c0⁻¹ * (c0*c0) := by rw [hcc,mul_one]
    _ = c0 := by group

/-- Prove the sign before substituting the dependent link endpoints.
The two endpoints are independent variables throughout the four cases. -/
private theorem p4Q2PZ37ASA_endpoint_sign
    (H : ℕ) (v s t : Vtx H) (q : J) (g : G) :
    p4Q2PZ37ARZ_coord q
      (p4Q2PZ37ASA_vertexFlip H v s * g * (p4Q2PZ37ASA_vertexFlip H v t)⁻¹) =
      (-1 : ℝ)^((if s = v then 1 else 0) + (if t = v then 1 else 0)) *
        p4Q2PZ37ARZ_coord q g := by
  classical
  have hm : ((p4Q2PZ37ASA_vertexFlip H v s * g *
      (p4Q2PZ37ASA_vertexFlip H v t)⁻¹ : G) : Mat) =
      if (s = v ↔ t = v) then (g : Mat) else -(g : Mat) := by
    change ((p4Q2PZ37ASA_vertexFlip H v s : G) : Mat) * (g : Mat) *
      (((p4Q2PZ37ASA_vertexFlip H v t)⁻¹ : G) : Mat) = _
    by_cases hs : s = v <;> by_cases ht : t = v <;>
      simp [p4Q2PZ37ASA_vertexFlip,hs,ht,p4Q2PZ37ASA_center_inv,
        p4Q2PZ35D4_centralMinusOne_coe]
  unfold p4Q2PZ37ARZ_coord
  rw [hm]
  by_cases hs : s = v <;> by_cases ht : t = v <;>
    by_cases hq : q.2 = true <;> simp [hs,ht,hq]

/-- Coordinate sign under the actual central gauge action at v. -/
theorem p4Q2PZ37ASA_coord_flip
    (H : ℕ) (v : Vtx H) (l : Link H) (q : J) (A : Cfg H 2) :
    p4Q2PZ37ARZ_coord q (GT H 2 (p4Q2PZ37ASA_vertexFlip H v) A l) =
      (-1 : ℝ)^(p4Q2PZ37ASA_incidence H v l) * p4Q2PZ37ARZ_coord q (A l) := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_apply]
  exact p4Q2PZ37ASA_endpoint_sign H v l.1
    (periodicHypercubicEvenSpatialSliceShift H l.1 l.2) q (A l)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_coord_flip

private theorem p4Q2PZ37ASA_multiset_sign
    {I : Type} (s : Multiset I) (a b : I → ℝ) (z : ℝ)
    (h : ∀ q, a q = z*b q) :
    (s.map a).prod = z^s.card * (s.map b).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,h q,ih,pow_succ]
      ring

/-- Explicit left and right factors using the ARX local symmetric index. -/
def p4Q2PZ37ASA_weightedLeft (H : ℕ) (beta : ℝ) (m : ℕ)
    (j : Link H → Idx m) (A : Cfg H 2) : ℝ :=
  W H 2 beta A * ∏ l : Link H, p4Q2PZ37ASA_left beta (j l) (A l)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_weightedLeft

def p4Q2PZ37ASA_weightedRight (H : ℕ) (beta : ℝ) (m : ℕ)
    (j : Link H → Idx m) (A : Cfg H 2) : ℝ :=
  W H 2 beta A * ∏ l : Link H, p4Q2PZ37ASA_right (j l) (A l)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_weightedRight

theorem p4Q2PZ37ASA_weightedLeft_cont
    (H : ℕ) (beta : ℝ) (m : ℕ) (j : Link H → Idx m) :
    Continuous (p4Q2PZ37ASA_weightedLeft H beta m j) := by
  exact (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 beta).mul
    (p4Q2PZ37ASA_cont_prod Finset.univ _
      (fun l => (p4Q2PZ37ASA_left_cont beta (j l)).comp (continuous_apply l)))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_weightedLeft_cont

theorem p4Q2PZ37ASA_weightedRight_cont
    (H : ℕ) (beta : ℝ) (m : ℕ) (j : Link H → Idx m) :
    Continuous (p4Q2PZ37ASA_weightedRight H beta m j) := by
  exact (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 beta).mul
    (p4Q2PZ37ASA_cont_prod Finset.univ _
      (fun l => (p4Q2PZ37ASA_right_cont (j l)).comp (continuous_apply l)))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_weightedRight_cont

/-- Exact actual partial slab, with explicit indices instead of arbitrary
existentially chosen continuous factors. -/
theorem p4Q2PZ37ASA_partialSlab_indexed
    (H : ℕ) (beta : ℝ) (m : ℕ) (A B : Cfg H 2) :
    p4Q2PZ37ARU_partialSlab H beta m A B =
      ∑ j : Link H → Idx m, p4Q2PZ37ASA_weightedLeft H beta m j A *
        p4Q2PZ37ASA_weightedRight H beta m j B := by
  classical
  have hlist : ((L H).map (fun l => kp 2 beta m (A l) (B l))).prod =
      ∏ l : Link H, kp 2 beta m (A l) (B l) := by
    unfold periodicHypercubicEvenSpatialSliceLinkList
    rw [Finset.prod_map_toList]
    apply Finset.prod_congr
    · apply Finset.ext
      intro l
      simp only [Finset.mem_univ]
    · intro l _
      rfl
  unfold p4Q2PZ37ARU_partialSlab
  rw [hlist]
  exact p4Q2PZ37ASA_weighted_product (W H 2 beta A) (W H 2 beta B)
    (fun l : Link H => kp 2 beta m (A l) (B l))
    (fun (l : Link H) (i : Idx m) => p4Q2PZ37ASA_left beta i (A l))
    (fun (l : Link H) (i : Idx m) => p4Q2PZ37ASA_right i (B l))
    (fun l => p4Q2PZ37ASA_local_expansion beta m (A l) (B l))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_partialSlab_indexed

theorem p4Q2PZ37ASA_weightedRight_flip
    (H : ℕ) (beta : ℝ) (m : ℕ) (j : Link H → Idx m)
    (v : Vtx H) (A : Cfg H 2) :
    p4Q2PZ37ASA_weightedRight H beta m j (GT H 2 (p4Q2PZ37ASA_vertexFlip H v) A) =
      (-1 : ℝ)^(p4Q2PZ37ASA_vertexDegree H m v j) *
        p4Q2PZ37ASA_weightedRight H beta m j A := by
  classical
  let C := GT H 2 (p4Q2PZ37ASA_vertexFlip H v) A
  have hl (l : Link H) : p4Q2PZ37ASA_right (j l) (C l) =
      (-1 : ℝ)^(p4Q2PZ37ASA_incidence H v l * (j l).1.val) *
        p4Q2PZ37ASA_right (j l) (A l) := by
    unfold p4Q2PZ37ASA_right
    rw [pow_mul]
    have hh := p4Q2PZ37ASA_multiset_sign (j l).2.val
      (fun q : J => p4Q2PZ37ARZ_coord q (C l))
      (fun q : J => p4Q2PZ37ARZ_coord q (A l))
      ((-1 : ℝ)^(p4Q2PZ37ASA_incidence H v l))
      (fun q => p4Q2PZ37ASA_coord_flip H v l q A)
    have hc : (j l).2.val.card = (j l).1.val := (j l).2.property
    rw [hc] at hh
    exact hh
  have hp : (∏ l : Link H, p4Q2PZ37ASA_right (j l) (C l)) =
      ∏ l : Link H, (-1 : ℝ)^(p4Q2PZ37ASA_incidence H v l * (j l).1.val) *
        p4Q2PZ37ASA_right (j l) (A l) :=
    Finset.prod_congr rfl (fun l _ => hl l)
  have hw : W H 2 beta C = W H 2 beta A :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_gaugeInvariant
      H 2 beta (p4Q2PZ37ASA_vertexFlip H v) A
  change W H 2 beta C * (∏ l : Link H, p4Q2PZ37ASA_right (j l) (C l)) = _
  rw [hw,hp,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  unfold p4Q2PZ37ASA_vertexDegree p4Q2PZ37ASA_weightedRight
  ring

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_weightedRight_flip

/-- Actual L2 class of each indexed continuous right factor. -/
def p4Q2PZ37ASA_rightLp (H : ℕ) (beta : ℝ) (m : ℕ)
    (j : Link H → Idx m) : Lp ℝ 2 (Mu H 2) :=
  ContinuousMap.toLp 2 (Mu H 2) ℝ
    ⟨p4Q2PZ37ASA_weightedRight H beta m j,p4Q2PZ37ASA_weightedRight_cont H beta m j⟩

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_rightLp

theorem p4Q2PZ37ASA_rightLp_odd
    (H : ℕ) (beta : ℝ) (m : ℕ) (j : Link H → Idx m) (v : Vtx H)
    (ho : Odd (p4Q2PZ37ASA_vertexDegree H m v j)) :
    Pull H 2 (p4Q2PZ37ASA_vertexFlip H v) (p4Q2PZ37ASA_rightLp H beta m j) =
      -(p4Q2PZ37ASA_rightLp H beta m j) := by
  apply p4Q2PZ37ARZ_ae_odd_pullback H (p4Q2PZ37ASA_vertexFlip H v)
    (p4Q2PZ37ASA_rightLp H beta m j) (p4Q2PZ37ASA_weightedRight H beta m j)
  · exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (Mu H 2)
      ⟨p4Q2PZ37ASA_weightedRight H beta m j,p4Q2PZ37ASA_weightedRight_cont H beta m j⟩
  · intro A
    rw [p4Q2PZ37ASA_weightedRight_flip H beta m j v A,ho.neg_one_pow,neg_one_mul]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_rightLp_odd

theorem p4Q2PZ37ASA_rightLp_inner_zero
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (m : ℕ)
    (j : Link H → Idx m) (v : Vtx H)
    (ho : Odd (p4Q2PZ37ASA_vertexDegree H m v j))
    (x : K H 2 h2 beta hb) :
    inner ℝ (p4Q2PZ37ASA_rightLp H beta m j) (Emb H 2 h2 beta hb x) = 0 := by
  exact p4Q2PZ37ARZ_gaugeOdd_inner H beta hb (p4Q2PZ37ASA_rightLp H beta m j)
    (p4Q2PZ37ASA_vertexFlip H v) (p4Q2PZ37ASA_rightLp_odd H beta m j v ho) x

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASA_rightLp_inner_zero

end
end MGAP4D.MathlibAnalytic
