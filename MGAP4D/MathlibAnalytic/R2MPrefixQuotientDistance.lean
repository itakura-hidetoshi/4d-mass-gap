import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Changing the left representative by zero-distance does not change the
finite-prefix pseudo-distance. -/
theorem r2m_prefix_pseudo_distance_eq_of_zero_distance_left
    (N : ℕ)
    {x x' y : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxx' : r2mPrefixZeroDistanceRel N x x') :
    r2mPrefixPseudoDistance N x y = r2mPrefixPseudoDistance N x' y := by
  unfold r2mPrefixZeroDistanceRel at hxx'
  apply le_antisymm
  · have htri := r2m_prefix_pseudo_distance_triangle N x x' y
    simpa [hxx'] using htri
  · have hx'x : r2mPrefixPseudoDistance N x' x = 0 := by
      simpa [r2mPrefixZeroDistanceRel] using
        (r2m_prefix_zero_distance_symm N (x := x) (y := x') hxx')
    have htri := r2m_prefix_pseudo_distance_triangle N x' x y
    simpa [hx'x] using htri

/-- Changing the right representative by zero-distance does not change the
finite-prefix pseudo-distance. -/
theorem r2m_prefix_pseudo_distance_eq_of_zero_distance_right
    (N : ℕ)
    {x y y' : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hyy' : r2mPrefixZeroDistanceRel N y y') :
    r2mPrefixPseudoDistance N x y = r2mPrefixPseudoDistance N x y' := by
  calc
    r2mPrefixPseudoDistance N x y
        = r2mPrefixPseudoDistance N y x :=
      r2m_prefix_pseudo_distance_symm N x y
    _ = r2mPrefixPseudoDistance N y' x :=
      r2m_prefix_pseudo_distance_eq_of_zero_distance_left N hyy'
    _ = r2mPrefixPseudoDistance N x y' := by
      rw [r2m_prefix_pseudo_distance_symm N x y']

/-- Changing both representatives by zero-distance does not change the
finite-prefix pseudo-distance. -/
theorem r2m_prefix_pseudo_distance_eq_of_zero_distance_both
    (N : ℕ)
    {x x' y y' : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxx' : r2mPrefixZeroDistanceRel N x x')
    (hyy' : r2mPrefixZeroDistanceRel N y y') :
    r2mPrefixPseudoDistance N x y = r2mPrefixPseudoDistance N x' y' := by
  calc
    r2mPrefixPseudoDistance N x y
        = r2mPrefixPseudoDistance N x' y :=
      r2m_prefix_pseudo_distance_eq_of_zero_distance_left N hxx'
    _ = r2mPrefixPseudoDistance N x' y' :=
      r2m_prefix_pseudo_distance_eq_of_zero_distance_right N hyy'

/-- Distance on the zero-distance quotient, induced by the finite-prefix
pseudo-distance.  It is defined by nested quotient lifting to make the
well-definedness obligations explicit. -/
def r2mPrefixQuotientDistance
    (N : ℕ) :
    R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N → ℝ :=
  fun q r =>
    Quotient.liftOn' q
      (fun x : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
        Quotient.liftOn' r
          (fun y : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
            r2mPrefixPseudoDistance N x y)
          (fun _ _ hyy' =>
            r2m_prefix_pseudo_distance_eq_of_zero_distance_right N hyy'))
      (fun _ _ hxx' => by
        refine Quotient.inductionOn' r ?_
        intro y
        exact r2m_prefix_pseudo_distance_eq_of_zero_distance_left N hxx')

/-- Evaluation of the quotient distance on representatives. -/
theorem r2m_prefix_quotient_distance_mk
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientDistance N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) =
      r2mPrefixPseudoDistance N x y := by
  rfl

/-- Nonnegativity of the quotient distance. -/
theorem r2m_prefix_quotient_distance_nonneg
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    0 ≤ r2mPrefixQuotientDistance N q r := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  rw [r2m_prefix_quotient_distance_mk]
  exact r2m_prefix_pseudo_distance_nonneg N x y

/-- Self-distance is zero on the quotient. -/
theorem r2m_prefix_quotient_distance_self
    (N : ℕ)
    (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q q = 0 := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_distance_mk]
  exact r2m_prefix_pseudo_distance_self N x

/-- Symmetry of the quotient distance. -/
theorem r2m_prefix_quotient_distance_symm
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientDistance N r q := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  repeat rw [r2m_prefix_quotient_distance_mk]
  exact r2m_prefix_pseudo_distance_symm N x y

/-- Triangle inequality for the quotient distance. -/
theorem r2m_prefix_quotient_distance_triangle
    (N : ℕ)
    (q r s : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q s ≤
      r2mPrefixQuotientDistance N q r +
        r2mPrefixQuotientDistance N r s := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  refine Quotient.inductionOn' s ?_
  intro z
  repeat rw [r2m_prefix_quotient_distance_mk]
  exact r2m_prefix_pseudo_distance_triangle N x y z

/-- Quotient-distance readiness: the finite-prefix pseudo-distance has been
transported to the zero-distance quotient and satisfies nonnegativity,
self-zero, symmetry, and triangle there. -/
def r2mPrefixQuotientDistanceReady : Prop :=
  r2mPrefixQuotientSeparationReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 ≤ r2mPrefixQuotientDistance N q r) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q q = 0) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientDistance N r q) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q s ≤
      r2mPrefixQuotientDistance N q r +
        r2mPrefixQuotientDistance N r s)

/-- The quotient distance surface is ready. -/
theorem r2m_prefix_quotient_distance_ready :
    r2mPrefixQuotientDistanceReady := by
  exact ⟨
    r2m_prefix_quotient_separation_ready,
    r2m_prefix_quotient_distance_nonneg,
    r2m_prefix_quotient_distance_self,
    r2m_prefix_quotient_distance_symm,
    r2m_prefix_quotient_distance_triangle⟩

/-- Boundary marker: quotient metric-style distance laws are available, while
Mathlib metric/normed typeclass promotion remains a later layer. -/
def r2mPrefixQuotientMetricTypeclassBoundaryHeld : Prop :=
  r2mPrefixQuotientDistanceReady ∧
  True

theorem r2m_prefix_quotient_metric_typeclass_boundary_held :
    r2mPrefixQuotientMetricTypeclassBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_distance_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
