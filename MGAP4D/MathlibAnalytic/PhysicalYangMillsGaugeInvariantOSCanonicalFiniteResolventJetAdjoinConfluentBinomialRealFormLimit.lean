import MGAP4D.MathlibAnalytic.ContinuousLinearMapFinitePositivePowerJetAdjoinConfluentBinomialNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventJetRealFormLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap
open StandardRealHilbertComplexification

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The finite-time normal form obtained by adjoining one new positive
multiplicity node to a finite positive resolvent jet. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
    {β : Type*}
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finitePositivePowerJetAdjoinConfluentBinomialNormalForm
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    s shift order c theta p

/-- The corresponding continuum finite-jet adjoin normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finitePositivePowerJetAdjoinConfluentBinomialNormalForm
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    s shift order c theta p

/-- At finite time, adjoining one repeated resolvent block to a finite positive
jet is exactly the closed termwise binomial normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    G.admissibleRescaledDefectResolventFinsetJetCombination
        hInnerSymmetric tau s shift (fun b => order b + 1) c *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau theta.property) ^ (p + 1) =
      G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
        hInnerSymmetric tau s shift order c theta p := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (ContinuousLinearMap.finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      s shift order c theta p hne
      (fun b hb =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau (shift b).property theta.property))

/-- The continuum finite positive jet satisfies the same adjoin identity. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    G.continuumResolventFinsetJetCombination
        T hP hInnerSymmetric hSelf s shift (fun b => order b + 1) c *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf theta.property) ^ (p + 1) =
      G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf s shift order c theta p := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination,
    VacuumSemigroupGapSlope.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (ContinuousLinearMap.finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      s shift order c theta p hne
      (fun b hb =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf (shift b).property theta.property))

/-- The finite-time adjoin normal form is exactly the finite word-sum obtained
by appending the new repeated block to every old replicated jet word. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
        hInnerSymmetric tau s shift order c theta p =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau s
        (fun b =>
          List.replicate (order b + 1) (shift b) ++
            List.replicate (p + 1) theta)
        c := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum] using
    (ContinuousLinearMap.finitePositivePowerJetAdjoinConfluentBinomialNormalForm_eq_finset_sum_smul_orderedProduct_append_replicate
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      s shift order c theta p hne
      (fun b hb =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau (shift b).property theta.property))

/-- The continuum adjoin normal form is the corresponding appended finite word-sum. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf s shift order c theta p =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf s
        (fun b =>
          List.replicate (order b + 1) (shift b) ++
            List.replicate (p + 1) theta)
        c := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm,
    VacuumSemigroupGapSlope.continuumResolventFinsetWordSum] using
    (ContinuousLinearMap.finitePositivePowerJetAdjoinConfluentBinomialNormalForm_eq_finset_sum_smul_orderedProduct_append_replicate
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      s shift order c theta p hne
      (fun b hb =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf (shift b).property theta.property))

/-- Finite-jet adjoin normal forms converge pointwise strongly after canonical
diagonal complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
            hInnerSymmetric tau s shift order c theta p) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf s shift order c theta p) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
            hInnerSymmetric tau s shift order c theta p) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s
            (fun b =>
              List.replicate (order b + 1) (shift b) ++
                List.replicate (p + 1) theta)
            c) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
      T hInnerSymmetric tau s shift order c theta p hne]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf s shift order c theta p) z =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s
            (fun b =>
              List.replicate (order b + 1) (shift b) ++
                List.replicate (p + 1) theta)
            c) z := by
    rw [G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
      T hP hInnerSymmetric hSelf s shift order c theta p hne]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf s
      (fun b =>
        List.replicate (order b + 1) (shift b) ++
          List.replicate (p + 1) theta)
      c z

/-- The continuum finite-jet adjoin normal form remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    diagonalComplexification
        (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf s shift order c theta p) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
    T hP hInnerSymmetric hSelf s shift order c theta p hne]
  exact
    G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf s
      (fun b =>
        List.replicate (order b + 1) (shift b) ++
          List.replicate (p + 1) theta)
      c

/-- The underlying bounded real operator of the finite-jet adjoin strong limit
exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf s shift order c theta p) := by
  rw [G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
    T hP hInnerSymmetric hSelf s shift order c theta p hne]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf s
      (fun b =>
        List.replicate (order b + 1) (shift b) ++
          List.replicate (p + 1) theta)
      c

/-- Any bounded real operator producing the same complex strong limit is exactly
the continuum finite-jet adjoin normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm_real_limit_eq_continuum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
              hInnerSymmetric tau s shift order c theta p) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
      T hP hInnerSymmetric hSelf s shift order c theta p := by
  have hRWord : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s
              (fun b =>
                List.replicate (order b + 1) (shift b) ++
                  List.replicate (p + 1) theta)
              c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z)) := by
    intro z
    have hSource :
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
              hInnerSymmetric tau s shift order c theta p) z) =
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s
              (fun b =>
                List.replicate (order b + 1) (shift b) ++
                  List.replicate (p + 1) theta)
              c) z) := by
      funext tau
      rw [G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
        T hInnerSymmetric tau s shift order c theta p hne]
    rw [← hSource]
    exact hR z
  calc
    R = G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf s
        (fun b =>
          List.replicate (order b + 1) (shift b) ++
            List.replicate (p + 1) theta)
        c :=
      G.admissibleRescaledDefectResolventFinsetWordSum_real_limit_eq_continuum
        T hP hInnerSymmetric hSelf s
        (fun b =>
          List.replicate (order b + 1) (shift b) ++
            List.replicate (p + 1) theta)
        c R hRWord
    _ = G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf s shift order c theta p :=
      (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm_eq_finsetWordSum_append_replicate
        T hP hInnerSymmetric hSelf s shift order c theta p hne).symm

/-- Actual OS real-form strong-limit package for adjoining one new positive
multiplicity node to an arbitrary finite positive resolvent jet. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteResolventJetAdjoinConfluentBinomialRealFormStrongLimitPackage
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ)
    (theta : G.BelowHalfMassShift)
    (p : ℕ)
    (hne : ∀ b ∈ s, (shift b).1 ≠ theta.1) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalForm
              hInnerSymmetric tau s shift order c theta p) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
              T hP hInnerSymmetric hSelf s shift order c theta p) z))) ∧
    diagonalComplexification
        (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf s shift order c theta p) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf s shift order c theta p) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf s shift order c theta p hne z
  constructor
  · exact
      G.continuumResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf s shift order c theta p hne
  · exact
      G.admissibleRescaledDefectResolventFinsetJetAdjoinConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf s shift order c theta p hne

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
