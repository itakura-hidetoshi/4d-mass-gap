import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormDistanceControl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If two quotient points are close in the installed distance, then their
norms are close. -/
theorem r2m_prefix_quotient_abs_norm_sub_le_of_dist_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (hqr : dist q r ≤ ε) :
    |‖q‖ - ‖r‖| ≤ ε := by
  exact le_trans (r2m_prefix_quotient_abs_norm_sub_le_dist_typeclass N q r) hqr

/-- Pointwise sequence form: metric closeness of two terms controls their norm
separation. -/
theorem r2m_prefix_quotient_norm_seq_abs_sub_le_of_dist_le_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (n m : ℕ) (ε : ℝ)
    (h : dist (u n) (u m) ≤ ε) :
    |‖u n‖ - ‖u m‖| ≤ ε := by
  exact r2m_prefix_quotient_abs_norm_sub_le_of_dist_le_typeclass N (u n) (u m) ε h

/-- Tail sequence form: a distance-Cauchy tail gives a norm-Cauchy tail. -/
theorem r2m_prefix_quotient_norm_tail_abs_sub_le_of_dist_tail_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (M : ℕ) (ε : ℝ)
    (h : ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) :
    ∀ n m : ℕ, M ≤ n → M ≤ m → |‖u n‖ - ‖u m‖| ≤ ε := by
  intro n m hn hm
  exact r2m_prefix_quotient_norm_seq_abs_sub_le_of_dist_le_typeclass N u n m ε
    (h n m hn hm)

/-- A one-reference upper norm estimate from distance control. -/
theorem r2m_prefix_quotient_norm_le_reference_norm_add_of_dist_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (hqr : dist q r ≤ ε) :
    ‖q‖ ≤ ‖r‖ + ε := by
  refine le_trans (r2m_prefix_quotient_norm_le_norm_add_dist_typeclass N q r) ?_
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hqr ‖r‖

/-- Sequence form of the reference upper norm estimate. -/
theorem r2m_prefix_quotient_norm_seq_le_reference_norm_add_of_dist_le_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (n k : ℕ) (ε : ℝ)
    (h : dist (u n) (u k) ≤ ε) :
    ‖u n‖ ≤ ‖u k‖ + ε := by
  exact r2m_prefix_quotient_norm_le_reference_norm_add_of_dist_le_typeclass N
    (u n) (u k) ε h

/-- Tail-to-reference norm control: if every tail point stays within `ε` of a
reference tail point, their norms are uniformly controlled by the reference
orm plus `ε`. -/
theorem r2m_prefix_quotient_norm_tail_le_reference_norm_add_of_dist_tail_typeclass
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (M k : ℕ) (ε : ℝ)
    (_hk : M ≤ k)
    (h : ∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) :
    ∀ n : ℕ, M ≤ n → ‖u n‖ ≤ ‖u k‖ + ε := by
  intro n hn
  exact r2m_prefix_quotient_norm_seq_le_reference_norm_add_of_dist_le_typeclass N
    u n k ε (h n hn)

/-- Cauchy-control surface for the quotient norm.  This is the bridge from
quotient metric estimates to scalar norm estimates used by later completion and
closed-operator arguments. -/
def r2mPrefixQuotientNormCauchyControlReady : Prop :=
  r2mPrefixQuotientNormDistanceControlReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    dist q r ≤ ε → |‖q‖ - ‖r‖| ≤ ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (M : ℕ) (ε : ℝ),
    (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) →
    ∀ n m : ℕ, M ≤ n → M ≤ m → |‖u n‖ - ‖u m‖| ≤ ε) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    dist q r ≤ ε → ‖q‖ ≤ ‖r‖ + ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (M k : ℕ) (ε : ℝ),
    M ≤ k →
    (∀ n : ℕ, M ≤ n → dist (u n) (u k) ≤ ε) →
    ∀ n : ℕ, M ≤ n → ‖u n‖ ≤ ‖u k‖ + ε)

/-- The quotient norm Cauchy-control surface is ready. -/
theorem r2m_prefix_quotient_norm_cauchy_control_ready :
    r2mPrefixQuotientNormCauchyControlReady := by
  exact ⟨
    r2m_prefix_quotient_norm_distance_control_ready,
    r2m_prefix_quotient_abs_norm_sub_le_of_dist_le_typeclass,
    r2m_prefix_quotient_norm_tail_abs_sub_le_of_dist_tail_typeclass,
    r2m_prefix_quotient_norm_le_reference_norm_add_of_dist_le_typeclass,
    r2m_prefix_quotient_norm_tail_le_reference_norm_add_of_dist_tail_typeclass⟩

/-- Boundary marker: quotient metric Cauchy control transports to scalar norm
Cauchy control. -/
def r2mPrefixQuotientNormCauchyControlBoundaryHeld : Prop :=
  r2mPrefixQuotientNormCauchyControlReady ∧
  True

theorem r2m_prefix_quotient_norm_cauchy_control_boundary_held :
    r2mPrefixQuotientNormCauchyControlBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_norm_cauchy_control_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
