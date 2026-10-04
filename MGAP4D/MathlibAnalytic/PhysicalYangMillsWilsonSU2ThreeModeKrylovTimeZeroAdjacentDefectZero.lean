import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovSummableAdjacentDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeProjectiveStrongLimit
import Mathlib.Tactic

/-!
# Eventual vanishing of the SU(2) time-zero adjacent refinement defect

The adjacent-defect route reduces H1-C3 existence to one-step refinement errors.
At natural time zero, the coherent Gram--Schmidt readout already gives more:
the finite three-mode projective synthesis is eventually exactly equal to one
fixed continuum synthesis.

Therefore consecutive time-zero Krylov vectors are eventually identical in the
common continuum carrier.  The exact finite-marginal distance identity from
#5096 then shows that the adjacent finite refinement defect at m = 0 is
eventually exactly zero, hence summable.

Thus any future adjacent-transfer perturbation estimate need only control the
genuine transfer mismatch; the initial-mode mismatch disappears eventually
under the existing coherent readout.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2KrylovTimeZeroAdjacentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2KrylovTimeZeroAdjacentCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2KrylovTimeZeroAdjacentSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2KrylovTimeZeroAdjacentMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2KrylovTimeZeroAdjacentBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2KrylovTimeZeroAdjacentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2KrylovTimeZeroAdjacentSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2KrylovTimeZeroAdjacentNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section TimeZeroAdjacent

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- At natural time zero, evolved synthesis is exactly the finite projective
continuum synthesis. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_zero_eq_finiteProjectiveContinuumSynthesis
    (n : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) :
    physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis
        Q R L n 0 c =
      physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
        Q R L n c := by
  simp [
    physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis,
    physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
  ]

/-- The time-zero k-th Krylov vector is the finite projective synthesis of the
corresponding standard basis vector. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_zero_eq_finiteProjectiveContinuumSynthesis_basisFun
    (n : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L n 0 k =
      physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
        Q R L n
        (EuclideanSpace.basisFun (Fin 3) ℝ k) := by
  rw [
    ← physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_basisFun
      Q R L n 0 k]
  exact
    physicalYangMillsSU2ThreeModeEvolvedProjectiveSynthesis_zero_eq_finiteProjectiveContinuumSynthesis
      Q R L n
      (EuclideanSpace.basisFun (Fin 3) ℝ k)

/-- Under the existing coherent readout, consecutive time-zero Krylov vectors
are eventually exactly equal. -/
theorem physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_zero_eq_succ_eventually
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (k : Fin 3) :
    ∀ᶠ n in atTop,
      physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n 0 k =
        physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L (n + 1) 0 k := by
  have hSame :=
    physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis_eq_eventually
      Q R L hInvariant C
  have hSameSucc :=
    (tendsto_add_atTop_nat 1).eventually hSame
  filter_upwards [hSame, hSameSucc] with n hn hns
  calc
    physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L n 0 k =
      physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
        Q R L n
        (EuclideanSpace.basisFun (Fin 3) ℝ k) :=
      physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_zero_eq_finiteProjectiveContinuumSynthesis_basisFun
        Q R L n k
    _ =
      physicalYangMillsSU2ThreeModeContinuumSynthesis
        Q R L hInvariant C
        (EuclideanSpace.basisFun (Fin 3) ℝ k) :=
      hn _
    _ =
      physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
        Q R L (n + 1)
        (EuclideanSpace.basisFun (Fin 3) ℝ k) :=
      (hns _).symm
    _ =
      physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
        Q R L (n + 1) 0 k :=
      (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_zero_eq_finiteProjectiveContinuumSynthesis_basisFun
        Q R L (n + 1) k).symm

/-- Hence the finite adjacent refinement defect at time zero is eventually
exactly zero. -/
theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_zero_eventually
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (k : Fin 3) :
    ∀ᶠ n in atTop,
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n 0 k = 0 := by
  filter_upwards
    [physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_zero_eq_succ_eventually
      Q R L hInvariant C k] with n hn
  calc
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n 0 k =
      dist
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L n 0 k)
        (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode
          Q R L (n + 1) 0 k) :=
      (physicalYangMillsSU2ThreeModeEvolvedProjectiveKrylovMode_dist_succ_eq_finiteAdjacentKrylovDefect
        Q R L n 0 k).symm
    _ = 0 := by rw [hn, dist_self]

/-- The time-zero adjacent defect is therefore summable without any
quantitative refinement estimate. -/
theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_zero_summable
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k) := by
  classical
  rcases eventually_atTop.1
      (physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_zero_eventually
        Q R L hInvariant C k) with ⟨N, hN⟩
  have hzero :
      ∀ n : ℕ, n ∉ Finset.range N →
        physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k = 0 := by
    intro n hn
    have hnN : N ≤ n := by
      exact Nat.le_of_not_gt (by
        intro hlt
        exact hn (by simpa [Finset.mem_range] using hlt))
    exact hN n hnN
  exact summable_of_ne_finset_zero hzero

end TimeZeroAdjacent

end

end MathlibAnalytic
end MGAP4D
