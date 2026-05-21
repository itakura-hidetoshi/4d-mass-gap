import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormCauchyControl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Lower reference estimate from one-step distance control: if `q` is within
`ε` of the reference `r`, then the norm of `q` lies above `‖r‖ - ε`. -/
theorem r2m_prefix_quotient_reference_norm_sub_le_norm_of_dist_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (hqr : dist q r ≤ ε) :
    ‖r‖ - ε ≤ ‖q‖ := by
  have habs : |‖q‖ - ‖r‖| ≤ ε :=
    r2m_prefix_quotient_abs_norm_sub_le_of_dist_le_typeclass N q r ε hqr
  have hneg : -(‖q‖ - ‖r‖) ≤ |‖q‖ - ‖r‖| := neg_le_abs (‖q‖ - ‖r‖)
  have hnegε : -(‖q‖ - ‖r‖) ≤ ε := le_trans hneg habs
  linarith

/-- Two-sided reference tube from one-step distance control. -/
theorem r2m_prefix_quotient_norm_mem_reference_tube_of_dist_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (hqr : dist q r ≤ ε) :
    ‖r‖ - ε ≤ ‖q‖ ∧ ‖q‖ ≤ ‖r‖ + ε := by
  constructor
  · exact r2m_prefix_quotient_reference_norm_sub_le_norm_of_dist_le_typeclass N q r ε hqr
  · exact r2m_prefix_quotient_norm_le_reference_norm_add_of_dist_le_typeclass N q r ε hqr

/-- Sequence form of the lower reference estimate. -/
theorem r2m_prefix_quotient_norm_seq_reference_sub_le_norm_of_dist_le_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (n k : ℕ) (ε : ℝ)
    (h : dist (u n) (u k) ≤ ε) :
    ‖u k‖ - ε ≤ ‖u n‖ := by
  exact r2m_prefix_quotient_reference_norm_sub_le_norm_of_dist_le_typeclass N
    (u n) (u k) ε h

/-- Sequence form of the two-sided reference tube. -/
theorem r2m_prefix_quotient_norm_seq_mem_reference_tube_of_dist_le_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (n k : ℕ) (ε : ℝ)
    (h : dist (u n) (u k) ≤ ε) :
    ‖u k‖ - ε ≤ ‖u n‖ ∧ ‖u n‖ ≤ ‖u k‖ + ε := by
  exact r2m_prefix_quotient_norm_mem_reference_tube_of_dist_le_typeclass N
    (u n) (u k) ε h

/-- Tail-to-reference lower tube estimate. -/
theorem r2m_prefix_quotient_norm_tail_reference_sub_le_norm_of_dist_tail_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (M k : ℕ) (ε : ℝ)
    (_hk : M ≤ k)
    (h : ∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) :
    ∀ n : ℕ, M ≤ n → ‖u k‖ - ε ≤ ‖u n‖ := by
  intro n hn
  exact r2m_prefix_quotient_norm_seq_reference_sub_le_norm_of_dist_le_typeclass N
    u n k ε (h n hn)

/-- Tail-to-reference two-sided tube estimate. -/
theorem r2m_prefix_quotient_norm_tail_mem_reference_tube_of_dist_tail_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (M k : ℕ) (ε : ℝ)
    (_hk : M ≤ k)
    (h : ∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) :
    ∀ n : ℕ, M ≤ n → ‖u k‖ - ε ≤ ‖u n‖ ∧ ‖u n‖ ≤ ‖u k‖ + ε := by
  intro n hn
  exact r2m_prefix_quotient_norm_seq_mem_reference_tube_of_dist_le_typeclass N
    u n k ε (h n hn)

/-- Tail tube-control surface: metric tail control around a reference point
becomes a two-sided scalar tube for the quotient norms. -/
def r2mPrefixQuotientNormTailTubeControlReady : Prop :=
  r2mPrefixQuotientNormCauchyControlReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    dist q r ≤ ε → ‖r‖ - ε ≤ ‖q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    dist q r ≤ ε → ‖r‖ - ε ≤ ‖q‖ ∧ ‖q‖ ≤ ‖r‖ + ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (M k : ℕ) (ε : ℝ),
    M ≤ k →
    (∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) →
    ∀ n : ℕ, M ≤ n → ‖u k‖ - ε ≤ ‖u n‖) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (M k : ℕ) (ε : ℝ),
    M ≤ k →
    (∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) →
    ∀ n : ℕ, M ≤ n → ‖u k‖ - ε ≤ ‖u n‖ ∧ ‖u n‖ ≤ ‖u k‖ + ε)

/-- The quotient norm tail tube-control surface is ready. -/
theorem r2m_prefix_quotient_norm_tail_tube_control_ready :
    r2mPrefixQuotientNormTailTubeControlReady := by
  exact ⟨
    r2m_prefix_quotient_norm_cauchy_control_ready,
    r2m_prefix_quotient_reference_norm_sub_le_norm_of_dist_le_typeclass,
    r2m_prefix_quotient_norm_mem_reference_tube_of_dist_le_typeclass,
    r2m_prefix_quotient_norm_tail_reference_sub_le_norm_of_dist_tail_typeclass,
    r2m_prefix_quotient_norm_tail_mem_reference_tube_of_dist_tail_typeclass⟩

/-- Boundary marker: metric tail control has been transported into scalar norm
tube control. -/
def r2mPrefixQuotientNormTailTubeControlBoundaryHeld : Prop :=
  r2mPrefixQuotientNormTailTubeControlReady ∧
  True

theorem r2m_prefix_quotient_norm_tail_tube_control_boundary_held :
    r2mPrefixQuotientNormTailTubeControlBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_norm_tail_tube_control_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
