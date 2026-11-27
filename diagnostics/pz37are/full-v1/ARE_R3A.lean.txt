import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalProjectedPairTransferMomentV5_PZ37ARD
import MGAP4D.MathlibAnalytic.PositiveWeightedMomentRatioEndpoint
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARE — actual projected-moment ratios and full excitation edge

Use the genuine ARD spectral sums, not a selected probe or a substituted
operator. The weight of an eigenbasis coordinate is its eigenvalue squared;
every positive eigenvalue is visible. Finite ratios give lower bounds on
the squared operator norm, not upper bounds. Reuse the existing abstract
positive weighted moment endpoint theorem. Keep the zero operator case
separate. No volume-uniform gap or continuum claim is made.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe u i

private theorem p4Q2PZ37ARE_sum_nonneg {ι : Type i}
    (f : ι → ℝ) (q : ℝ) (hf : ∀ k, 0 ≤ f k) (hs : HasSum f q) :
    0 ≤ q := by
  have h := sum_le_hasSum (∅ : Finset ι) (fun k _ => hf k) hs
  simpa using h

private theorem p4Q2PZ37ARE_coordinate_le {ι : Type i}
    (rho : ι → ℝ) (h0 : ∀ k, 0 ≤ rho k) (n : ℕ) (q : ℝ)
    (hs : HasSum (fun k => (rho k)^(2*(n+1))) q) (k : ι) :
    (rho k)^(2*(n+1)) ≤ q := by
  classical
  have h := sum_le_hasSum ({k} : Finset ι)
    (fun j _ => pow_nonneg (h0 j) _) hs
  simpa using h

private theorem p4Q2PZ37ARE_logConvex_aux {ι : Type i}
    (rho : ι → ℝ) (h0 : ∀ k, 0 ≤ rho k) (n : ℕ) (a b c : ℝ)
    (ha : HasSum (fun k => (rho k)^(2*(n+1))) a)
    (hb : HasSum (fun k => (rho k)^(2*(n+2))) b)
    (hc : HasSum (fun k => (rho k)^(2*(n+3))) c) :
    b^2 ≤ a*c := by
  have ha0 := p4Q2PZ37ARE_sum_nonneg _ _ (fun k => pow_nonneg (h0 k) _) ha
  have hb0 := p4Q2PZ37ARE_sum_nonneg _ _ (fun k => pow_nonneg (h0 k) _) hb
  have hc0 := p4Q2PZ37ARE_sum_nonneg _ _ (fun k => pow_nonneg (h0 k) _) hc
  have hfin (s : Finset ι) :
      (∑ k ∈ s, (rho k)^(2*(n+2))) ≤ Real.sqrt a * Real.sqrt c := by
    have hA := sum_le_hasSum s (fun k _ => pow_nonneg (h0 k) _) ha
    have hC := sum_le_hasSum s (fun k _ => pow_nonneg (h0 k) _) hc
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt s
      (fun k => (rho k)^(n+1)) (fun k => (rho k)^(n+3))
    simp only [← pow_add, ← pow_mul,
      show (n+1)+(n+3)=2*(n+2) by omega,
      show (n+1)*2=2*(n+1) by omega,
      show (n+3)*2=2*(n+3) by omega] at hCS
    exact hCS.trans (mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hC)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hB := hasSum_le_of_sum_le hb hfin
  have hsq := pow_le_pow_left₀ hb0 hB 2
  rw [mul_pow,Real.sq_sqrt ha0,Real.sq_sqrt hc0] at hsq
  exact hsq

private theorem p4Q2PZ37ARE_basis_norm_le {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} (T : E →L[ℝ] E) (b : HilbertBasis ι ℝ E)
    (rho : ι → ℝ) (he : ∀ k, T (b k) = rho k • b k)
    (hSym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (r : ℝ) (hr : 0 ≤ r) (h0 : ∀ k, 0 ≤ rho k)
    (hBound : ∀ k, rho k ≤ r) : ‖T‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound T hr
  intro x
  have hx := b.hasSum_inner_mul_inner x x
  have hy := b.hasSum_inner_mul_inner (T x) (T x)
  rw [real_inner_self_eq_norm_sq] at hx hy
  have hs : ‖T x‖^2 ≤ r^2 * ‖x‖^2 := by
    apply hasSum_le_of_sum_le hy
    intro s
    have hpart : (∑ k ∈ s, inner ℝ x (b k) * inner ℝ (b k) x) ≤ ‖x‖^2 :=
      sum_le_hasSum s (fun k _ => by
        rw [real_inner_comm (b k) x]
        exact mul_self_nonneg _) hx
    calc
      (∑ k ∈ s, inner ℝ (T x) (b k) * inner ℝ (b k) (T x)) ≤
          r^2 * (∑ k ∈ s, inner ℝ x (b k) * inner ℝ (b k) x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        have htx : inner ℝ (T x) (b k) = rho k * inner ℝ x (b k) := by
          rw [hSym x (b k),he k,real_inner_smul_right]
        have hxt : inner ℝ (b k) (T x) = rho k * inner ℝ (b k) x := by
          rw [← hSym (b k) x,he k,real_inner_smul_left]
        rw [htx,hxt,real_inner_comm (b k) x]
        calc
          _ = (rho k)^2 * (inner ℝ (b k) x)^2 := by ring
          _ ≤ r^2 * (inner ℝ (b k) x)^2 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h0 k) (hBound k) 2)
              (sq_nonneg _)
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpart (sq_nonneg r)
  have hsq : ‖T x‖^2 ≤ (r*‖x‖)^2 := by
    rw [mul_pow]
    exact hs
  have h := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg hr (norm_nonneg x))] at h
  exact h

private theorem p4Q2PZ37ARE_exists_pos {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} (T : E →L[ℝ] E) (b : HilbertBasis ι ℝ E)
    (rho : ι → ℝ) (he : ∀ k, T (b k) = rho k • b k)
    (hSym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (h0 : ∀ k, 0 ≤ rho k) (hT : T ≠ 0) : ∃ k, 0 < rho k := by
  by_contra h
  have hz (k : ι) : rho k ≤ 0 := le_of_not_gt (fun hk => h ⟨k,hk⟩)
  have hn := p4Q2PZ37ARE_basis_norm_le T b rho he hSym 0 le_rfl h0 hz
  exact hT (norm_eq_zero.mp (le_antisymm hn (norm_nonneg T)))

private theorem p4Q2PZ37ARE_visible_upper_aux {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} (T : E →L[ℝ] E) (b : HilbertBasis ι ℝ E)
    (rho : ι → ℝ) (he : ∀ k, T (b k) = rho k • b k)
    (hSym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (h0 : ∀ k, 0 ≤ rho k) (hT : T ≠ 0)
    (q : ℝ) (hq : ∀ k, 0 < (rho k)^2 → (rho k)^2 ≤ q) :
    ‖T‖^2 ≤ q := by
  obtain ⟨k,hk⟩ := p4Q2PZ37ARE_exists_pos T b rho he hSym h0 hT
  have hq0 : 0 ≤ q := (sq_nonneg (rho k)).trans (hq k (pow_pos hk 2))
  have hAll (j : ι) : rho j ≤ Real.sqrt q := by
    by_cases hj : rho j = 0
    · rw [hj]
      exact Real.sqrt_nonneg _
    · exact Real.le_sqrt_of_sq_le (hq j (pow_pos (lt_of_le_of_ne (h0 j) (Ne.symm hj)) 2))
  have hn := p4Q2PZ37ARE_basis_norm_le T b rho he hSym
    (Real.sqrt q) (Real.sqrt_nonneg _) h0 hAll
  have hsq := pow_le_pow_left₀ (norm_nonneg T) hn 2
  rwa [Real.sq_sqrt hq0] at hsq

private theorem p4Q2PZ37ARE_ratio_mono_aux (m : ℕ → ℝ)
    (hp : ∀ n, 0 < m n)
    (hc : ∀ n, m (n+1)^2 ≤ m n * m (n+2)) :
    Monotone (fun n => m (n+1) / m n) := by
  apply monotone_nat_of_le_succ
  intro n
  apply (div_le_div_iff₀ (hp n) (hp (n+1))).2
  simpa only [pow_two,mul_comm] using hc n

private theorem p4Q2PZ37ARE_ratio_limit_aux {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} (T : E →L[ℝ] E) (b : HilbertBasis ι ℝ E)
    (rho : ι → ℝ) (he : ∀ k, T (b k) = rho k • b k)
    (hSym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (h0 : ∀ k, 0 ≤ rho k) (hT : T ≠ 0)
    (m : ℕ → ℝ) (hs : ∀ n, HasSum (fun k => (rho k)^(2*(n+1))) (m n))
    (hUpper : ∀ n, m (n+1) ≤ ‖T‖^2 * m n) :
    Tendsto (fun n => m (n+1) / m n) atTop (𝓝 (‖T‖^2)) := by
  obtain ⟨k,hk⟩ := p4Q2PZ37ARE_exists_pos T b rho he hSym h0 hT
  have hp (n : ℕ) : 0 < m n :=
    (pow_pos hk _).trans_le (p4Q2PZ37ARE_coordinate_le rho h0 n _ (hs n) k)
  have hc (n : ℕ) : m (n+1)^2 ≤ m n * m (n+2) :=
    p4Q2PZ37ARE_logConvex_aux rho h0 n _ _ _ (hs n) (hs (n+1)) (hs (n+2))
  refine positiveWeightedMomentRatio_tendsto_of_supremum m
    (fun k => (rho k)^2) (fun k => (rho k)^2) (‖T‖^2)
    hp ?_ (p4Q2PZ37ARE_ratio_mono_aux m hp hc) ?_ ?_
  · intro j hj n
    have h := p4Q2PZ37ARE_coordinate_le rho h0 n _ (hs n) j
    rw [show 2*(n+1) = 2+2*n by omega,pow_add,pow_mul] at h
    exact h
  · intro n
    exact (div_le_iff₀ (hp n)).2 (hUpper n)
  · exact p4Q2PZ37ARE_visible_upper_aux T b rho he hSym h0 hT

private theorem p4Q2PZ37ARE_norm_zero_aux {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : T = 0) : ‖T‖ = 0 := by
  subst T
  exact ContinuousLinearMap.opNorm_zero

private theorem p4Q2PZ37ARE_two_pos : 0 < (2 : ℕ) := by decide

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Pair" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
local notation "Dec" => periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "OO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure
local notation "EH" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "PF" => p4Q2PZ37AQW_partitionFactor
local notation "Res" => p4Q2PZ37AQX_relativeResidual
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry

local instance p4Q2PZ37ARE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ARE_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ARE_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ARE_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ARE_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ARE_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ARE_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ARE_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ARE_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ARE_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local notation "h2" => p4Q2PZ37ARE_two_pos
local notation "M" => p4Q2PZ37ARD_pairMoment
local notation "S" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator

private theorem p4Q2PZ37ARE_step_symm (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    ∀ x y : K H 2 h2 beta hb, inner ℝ (Step H 2 h2 beta hb x) y =
      inner ℝ x (Step H 2 h2 beta hb y) := by
  intro x y
  let A : Phys H 2 →L[ℝ] Phys H 2 := S H 2 h2 beta hb
  have hs : (A : Phys H 2 →ₗ[ℝ] Phys H 2).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 h2 beta hb
  change inner ℝ (A (x : Phys H 2)) (y : Phys H 2) =
    inner ℝ (x : Phys H 2) (A (y : Phys H 2))
  exact hs (x : Phys H 2) (y : Phys H 2)

private theorem p4Q2PZ37ARE_eigen_nonneg
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    ∀ k, 0 ≤ rho k := fun k =>
  (p4Q2PZ37ARA_eigenvalue_bounds H beta hb (b k) (rho k)
    (b.orthonormal.norm_eq_one k) (he k)).1

theorem p4Q2PZ37ARE_moment_logConvex
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (n : ℕ) :
    M H beta hb (n+1)^2 ≤ M H beta hb n * M H beta hb (n+2) := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have h0 := @p4Q2PZ37ARE_eigen_nonneg H beta hb ι b rho he
  have ha := @p4Q2PZ37ARD_moment_hasSum H beta hb n ι b rho he
  have hm := @p4Q2PZ37ARD_moment_hasSum H beta hb (n+1) ι b rho he
  have hc := @p4Q2PZ37ARD_moment_hasSum H beta hb (n+2) ι b rho he
  exact p4Q2PZ37ARE_logConvex_aux rho h0 n _ _ _ ha hm hc

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_logConvex

/-- Every nonzero excitation operator has a positive visible coordinate. -/
theorem p4Q2PZ37ARE_moment_pos
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb ≠ 0) (n : ℕ) :
    0 < M H beta hb n := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have h0 := @p4Q2PZ37ARE_eigen_nonneg H beta hb ι b rho he
  have hSym := p4Q2PZ37ARE_step_symm H beta hb
  obtain ⟨k,hk⟩ := @p4Q2PZ37ARE_exists_pos
    ↥(K H 2 h2 beta hb) inferInstance inferInstance ι
    (Step H 2 h2 beta hb) b rho he hSym h0 hT
  have hm := @p4Q2PZ37ARD_moment_hasSum H beta hb n ι b rho he
  exact (pow_pos hk _).trans_le (p4Q2PZ37ARE_coordinate_le rho h0 n _ hm k)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_pos

theorem p4Q2PZ37ARE_moment_eq_zero_of_step_zero
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb = 0) (n : ℕ) :
    M H beta hb n = 0 := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have hz (k : ι) : rho k = 0 := by
    have hr := p4Q2PZ37ARA_eigenvalue_bounds H beta hb (b k) (rho k)
      (b.orthonormal.norm_eq_one k) (he k)
    have hnorm : ‖Step H 2 h2 beta hb‖ = 0 :=
      @p4Q2PZ37ARE_norm_zero_aux
        ↥(K H 2 h2 beta hb) inferInstance inferInstance
        (Step H 2 h2 beta hb) hT
    exact le_antisymm (hr.2.trans_eq hnorm) hr.1
  have hm := @p4Q2PZ37ARD_moment_hasSum H beta hb n ι b rho he
  have hf : (fun k : ι => (rho k)^(2*(n+1))) = fun _ => 0 := by
    funext k
    rw [hz k,zero_pow (by omega : 2*(n+1) ≠ 0)]
  rw [hf] at hm
  exact hm.unique hasSum_zero

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_eq_zero_of_step_zero

theorem p4Q2PZ37ARE_moment_ratio_mono
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb ≠ 0) :
    Monotone (fun n : ℕ => M H beta hb (n+1) / M H beta hb n) := by
  exact p4Q2PZ37ARE_ratio_mono_aux (M H beta hb)
    (p4Q2PZ37ARE_moment_pos H beta hb hT) (p4Q2PZ37ARE_moment_logConvex H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_ratio_mono

private theorem p4Q2PZ37ARE_step_upper
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (n : ℕ) :
    M H beta hb (n+1) ≤ ‖Step H 2 h2 beta hb‖^2 * M H beta hb n := by
  have h := p4Q2PZ37ARD_moment_shift_bound H beta hb n (n+1) (by omega)
  rw [show n+1-n=1 by omega] at h
  simpa only [mul_one] using h

/-- Finite ratios are LOWER bounds for the squared excitation norm. -/
theorem p4Q2PZ37ARE_moment_ratio_le_normSq
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb ≠ 0) (n : ℕ) :
    M H beta hb (n+1) / M H beta hb n ≤ ‖Step H 2 h2 beta hb‖^2 := by
  exact (div_le_iff₀ (p4Q2PZ37ARE_moment_pos H beta hb hT n)).2
    (p4Q2PZ37ARE_step_upper H beta hb n)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_ratio_le_normSq

/-- No selected probe is substituted: every nonzero complete-basis
coordinate is visible with weight equal to its eigenvalue squared. -/
theorem p4Q2PZ37ARE_visible_upper_controls_normSq
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb ≠ 0)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ) (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (q : ℝ) (hq : ∀ k, 0 < (rho k)^2 → (rho k)^2 ≤ q) :
    ‖Step H 2 h2 beta hb‖^2 ≤ q := by
  have h0 := @p4Q2PZ37ARE_eigen_nonneg H beta hb ι b rho he
  have hSym := p4Q2PZ37ARE_step_symm H beta hb
  exact @p4Q2PZ37ARE_visible_upper_aux
    ↥(K H 2 h2 beta hb) inferInstance inferInstance ι
    (Step H 2 h2 beta hb) b rho he hSym h0 hT q hq

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_visible_upper_controls_normSq

theorem p4Q2PZ37ARE_moment_ratio_tendsto_normSq
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (hT : Step H 2 h2 beta hb ≠ 0) :
    Tendsto (fun n : ℕ => M H beta hb (n+1) / M H beta hb n)
      atTop (𝓝 (‖Step H 2 h2 beta hb‖^2)) := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have h0 := @p4Q2PZ37ARE_eigen_nonneg H beta hb ι b rho he
  have hSym := p4Q2PZ37ARE_step_symm H beta hb
  have hm (n : ℕ) := @p4Q2PZ37ARD_moment_hasSum H beta hb n ι b rho he
  exact @p4Q2PZ37ARE_ratio_limit_aux
    ↥(K H 2 h2 beta hb) inferInstance inferInstance ι
    (Step H 2 h2 beta hb) b rho he hSym h0 hT
    (M H beta hb) hm (p4Q2PZ37ARE_step_upper H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARE_moment_ratio_tendsto_normSq

end
end MGAP4D.MathlibAnalytic
