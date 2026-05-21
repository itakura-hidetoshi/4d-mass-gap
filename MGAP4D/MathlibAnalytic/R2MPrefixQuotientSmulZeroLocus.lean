import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulSeminormLawClosure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Zero locus of quotient scalar multiplication.  After quotient separation and
absolute homogeneity, `c • q` is the zero class exactly when either the scalar is
zero or the quotient point is the zero class. -/
theorem r2m_prefix_quotient_smul_eq_zero_class_iff
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N c q = r2mPrefixQuotientZeroClass N ↔
      c = 0 ∨ q = r2mPrefixQuotientZeroClass N := by
  constructor
  · intro hzero
    have hnorm :
        r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) = 0 := by
      exact (r2m_prefix_quotient_seminorm_eq_zero_iff N
        (r2mPrefixQuotientSmul N c q)).mpr hzero
    rw [r2m_prefix_quotient_seminorm_smul_abs_closed] at hnorm
    rcases mul_eq_zero.mp hnorm with hcabs | hqnorm
    · left
      exact abs_eq_zero.mp hcabs
    · right
      exact (r2m_prefix_quotient_seminorm_eq_zero_iff N q).mp hqnorm
  · intro h
    rcases h with hc | hq
    · rw [hc]
      exact r2m_prefix_quotient_zero_smul_eq_zero_class_closed N q
    · rw [hq]
      exact r2m_prefix_quotient_smul_zero_class_closed N c

/-- If the scalar is nonzero, quotient scalar multiplication has zero value only
at the zero class. -/
theorem r2m_prefix_quotient_smul_eq_zero_class_iff_of_ne_zero
    (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N c q = r2mPrefixQuotientZeroClass N ↔
      q = r2mPrefixQuotientZeroClass N := by
  rw [r2m_prefix_quotient_smul_eq_zero_class_iff]
  constructor
  · intro h
    rcases h with hc0 | hq
    · exact False.elim (hc hc0)
    · exact hq
  · intro hq
    exact Or.inr hq

/-- Scalar zero-locus readiness package. -/
def r2mPrefixQuotientSmulZeroLocusReady : Prop :=
  r2mPrefixQuotientSmulSeminormLawClosed ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N c q = r2mPrefixQuotientZeroClass N ↔
      c = 0 ∨ q = r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) {c : ℝ}, c ≠ 0 →
    ∀ q : R2MPrefixZeroDistanceQuotient N,
      r2mPrefixQuotientSmul N c q = r2mPrefixQuotientZeroClass N ↔
        q = r2mPrefixQuotientZeroClass N)

/-- The quotient scalar zero-locus surface is ready. -/
theorem r2m_prefix_quotient_smul_zero_locus_ready :
    r2mPrefixQuotientSmulZeroLocusReady := by
  exact ⟨
    r2m_prefix_quotient_smul_seminorm_law_closed,
    r2m_prefix_quotient_smul_eq_zero_class_iff,
    fun N {c} hc q =>
      r2m_prefix_quotient_smul_eq_zero_class_iff_of_ne_zero N (c := c) hc q⟩

/-- Boundary marker: scalar zero-locus is closed; additive quotient structure is
still held as the next algebraic layer. -/
def r2mPrefixQuotientAdditiveCompatibilityBoundaryHeld : Prop :=
  r2mPrefixQuotientSmulZeroLocusReady ∧
  True

theorem r2m_prefix_quotient_additive_compatibility_boundary_held :
    r2mPrefixQuotientAdditiveCompatibilityBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_smul_zero_locus_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
