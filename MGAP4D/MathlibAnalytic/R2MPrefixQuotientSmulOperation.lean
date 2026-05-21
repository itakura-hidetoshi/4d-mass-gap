import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulWellDefined

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Scalar multiplication on the finite-prefix zero-distance quotient.  This is
installed only after proving that scalar multiplication preserves the
zero-distance relation on representatives. -/
def r2mPrefixQuotientSmul
    (N : ℕ) (c : ℝ) :
    R2MPrefixZeroDistanceQuotient N → R2MPrefixZeroDistanceQuotient N :=
  fun q =>
    Quotient.liftOn' q
      (fun x : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
        Quotient.mk (r2mPrefixZeroDistanceSetoid N)
          (concreteL2GraphPairPrefixEnergyBoundedSmul c x))
      (fun _ _ hxx' => by
        apply Quotient.sound
        exact r2m_prefix_zero_distance_smul N c hxx')

/-- Evaluation of quotient scalar multiplication on a representative. -/
theorem r2m_prefix_quotient_smul_mk
    (N : ℕ) (c : ℝ)
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientSmul N c
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x) := by
  rfl

/-- The quotient scalar operation is available as a well-defined endomap for
each finite prefix and scalar. -/
def r2mPrefixQuotientSmulOperationReady : Prop :=
  r2mPrefixQuotientSmulWellDefinedReady ∧
  (∀ (N : ℕ) (c : ℝ),
    Nonempty (R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N)) ∧
  (∀ (N : ℕ) (c : ℝ)
      (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixQuotientSmul N c
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x))

/-- Readiness theorem for the quotient scalar operation. -/
theorem r2m_prefix_quotient_smul_operation_ready :
    r2mPrefixQuotientSmulOperationReady := by
  exact ⟨
    r2m_prefix_quotient_smul_well_defined_ready,
    fun N c => ⟨r2mPrefixQuotientSmul N c⟩,
    r2m_prefix_quotient_smul_mk⟩

/-- Boundary marker: quotient scalar multiplication is installed; additive
compatibility remains the next explicit algebraic obligation before vector-space
or normed-space promotion. -/
def r2mPrefixQuotientVectorStructureBoundaryHeld : Prop :=
  r2mPrefixQuotientSmulOperationReady ∧
  True

theorem r2m_prefix_quotient_vector_structure_boundary_held :
    r2mPrefixQuotientVectorStructureBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_smul_operation_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
