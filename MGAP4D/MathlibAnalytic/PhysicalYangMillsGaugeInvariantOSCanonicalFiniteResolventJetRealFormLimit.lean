import MGAP4D.MathlibAnalytic.ContinuousLinearMapFinitePowerJetCombination
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventAlgebraRealFormLimit

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

/-- The finite-time bounded real operator represented by a finite resolvent jet:
a finite real linear combination of arbitrary powers at finitely many labelled
below-half-mass shifts. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination
    {β : Type*}
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finitePowerJetCombination
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    s shift order c

/-- The corresponding continuum bounded real finite resolvent jet. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finitePowerJetCombination
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    s shift order c

/-- A finite-time resolvent jet is exactly the existing finite resolvent
word-sum obtained by repeating each shift according to its labelled order. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination_eq_finsetWordSum_replicate
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    G.admissibleRescaledDefectResolventFinsetJetCombination
        hInnerSymmetric tau s shift order c =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau s
        (fun b => List.replicate (order b) (shift b)) c := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum] using
    (ContinuousLinearMap.finitePowerJetCombination_eq_finset_sum_smul_orderedProduct_replicate
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      s shift order c)

/-- A continuum resolvent jet is exactly the corresponding finite continuum
resolvent word-sum of replicated nodes. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    G.continuumResolventFinsetJetCombination
        T hP hInnerSymmetric hSelf s shift order c =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf s
        (fun b => List.replicate (order b) (shift b)) c := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination,
    VacuumSemigroupGapSlope.continuumResolventFinsetWordSum] using
    (ContinuousLinearMap.finitePowerJetCombination_eq_finset_sum_smul_orderedProduct_replicate
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      s shift order c)

/-- Every finite resolvent jet converges pointwise strongly after canonical
diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_tendsto_continuum
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
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetJetCombination
            hInnerSymmetric tau s shift order c) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFinsetJetCombination
            T hP hInnerSymmetric hSelf s shift order c) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetJetCombination
            hInnerSymmetric tau s shift order c) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s
            (fun b => List.replicate (order b) (shift b)) c) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventFinsetJetCombination_eq_finsetWordSum_replicate
      T hInnerSymmetric tau s shift order c]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFinsetJetCombination
            T hP hInnerSymmetric hSelf s shift order c) z =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s
            (fun b => List.replicate (order b) (shift b)) c) z := by
    rw [G.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
      T hP hInnerSymmetric hSelf s shift order c]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf s
      (fun b => List.replicate (order b) (shift b)) c z

/-- Every continuum finite resolvent jet remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetJetCombinationDiagonalComplexification_mem_realForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    diagonalComplexification
        (G.continuumResolventFinsetJetCombination
          T hP hInnerSymmetric hSelf s shift order c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
    T hP hInnerSymmetric hSelf s shift order c]
  exact
    G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf s
      (fun b => List.replicate (order b) (shift b)) c

/-- The bounded real operator underlying the complex strong limit of a finite
resolvent jet exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_existsUnique_real_limit
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetJetCombination
            T hP hInnerSymmetric hSelf s shift order c) := by
  rw [G.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
    T hP hInnerSymmetric hSelf s shift order c]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf s
      (fun b => List.replicate (order b) (shift b)) c

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the corresponding continuum finite resolvent jet. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination_real_limit_eq_continuum
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
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetCombination
              hInnerSymmetric tau s shift order c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFinsetJetCombination
      T hP hInnerSymmetric hSelf s shift order c := by
  have hRWord : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s
              (fun b => List.replicate (order b) (shift b)) c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z)) := by
    intro z
    have hSource :
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetCombination
              hInnerSymmetric tau s shift order c) z) =
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s
              (fun b => List.replicate (order b) (shift b)) c) z) := by
      funext tau
      rw [G.admissibleRescaledDefectResolventFinsetJetCombination_eq_finsetWordSum_replicate
        T hInnerSymmetric tau s shift order c]
    rw [← hSource]
    exact hR z
  calc
    R = G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf s
        (fun b => List.replicate (order b) (shift b)) c :=
      G.admissibleRescaledDefectResolventFinsetWordSum_real_limit_eq_continuum
        T hP hInnerSymmetric hSelf s
        (fun b => List.replicate (order b) (shift b)) c R hRWord
    _ = G.continuumResolventFinsetJetCombination
        T hP hInnerSymmetric hSelf s shift order c :=
      (G.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
        T hP hInnerSymmetric hSelf s shift order c).symm

/-- Actual OS real-form strong-limit package for finite resolvent jet
combinations, allowing finitely many distinct nodes and arbitrary repeated-node
orders simultaneously. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteResolventJetRealFormStrongLimitPackage
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (shift : β → G.BelowHalfMassShift)
    (order : β → ℕ)
    (c : β → ℝ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetJetCombination
              hInnerSymmetric tau s shift order c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFinsetJetCombination
              T hP hInnerSymmetric hSelf s shift order c) z))) ∧
    diagonalComplexification
        (G.continuumResolventFinsetJetCombination
          T hP hInnerSymmetric hSelf s shift order c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetJetCombination
            T hP hInnerSymmetric hSelf s shift order c) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf s shift order c z
  constructor
  · exact
      G.continuumResolventFinsetJetCombinationDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf s shift order c
  · exact
      G.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf s shift order c

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
