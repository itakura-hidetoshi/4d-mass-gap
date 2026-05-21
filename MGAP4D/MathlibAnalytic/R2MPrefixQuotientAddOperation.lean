import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddCompatibility

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Addition on the finite-prefix zero-distance quotient.  The operation is
installed after proving that addition preserves zero-distance representatives. -/
def r2mPrefixQuotientAdd
    (N : ℕ) :
    R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N →
        R2MPrefixZeroDistanceQuotient N :=
  fun q r =>
    Quotient.liftOn' q
      (fun x : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
        Quotient.liftOn' r
          (fun y : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
            Quotient.mk (r2mPrefixZeroDistanceSetoid N)
              (concreteL2GraphPairPrefixEnergyBoundedAdd x y))
          (fun y y' hyy' => by
            apply Quotient.sound
            exact r2m_prefix_zero_distance_add_compat N
              (r2m_prefix_zero_distance_refl N x) hyy'))
      (fun x x' hxx' => by
        refine Quotient.inductionOn' r ?_
        intro y
        apply Quotient.sound
        exact r2m_prefix_zero_distance_add_compat N hxx'
          (r2m_prefix_zero_distance_refl N y))

/-- Evaluation of quotient addition on representatives. -/
theorem r2m_prefix_quotient_add_mk
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientAdd N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) := by
  rfl

/-- The quotient addition operation is available as a well-defined binary
operation. -/
def r2mPrefixQuotientAddOperationReady : Prop :=
  r2mPrefixQuotientAddCompatibilityReady ∧
  (∀ (N : ℕ),
    Nonempty (R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N →
        R2MPrefixZeroDistanceQuotient N)) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixQuotientAdd N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y))

/-- The quotient addition operation is ready. -/
theorem r2m_prefix_quotient_add_operation_ready :
    r2mPrefixQuotientAddOperationReady := by
  exact ⟨
    r2m_prefix_quotient_add_compatibility_ready,
    fun N => ⟨r2mPrefixQuotientAdd N⟩,
    r2m_prefix_quotient_add_mk⟩

end

end MathlibAnalytic
end MGAP4D
