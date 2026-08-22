import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSReflectedGapToCanonicalBoundaryGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The actual finite Wilson OS transfer restricted to the complete
vacuum-orthogonal excitation sector.  This is the finite-side operator whose
norm is exactly reproduced by the corrected canonical boundary transfer. -/
noncomputable def finiteVacuumOrthogonalTransferLinearMap
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert →ₗ[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert where
  toFun := fun psi =>
    ⟨C.finiteOperator n t
        (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n), by
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      have hSymmetric :
          (C.finitePhysicalSemigroup n).IsInnerSymmetric :=
        (hExchange n).toPhysicalSemigroup_isInnerSymmetric
      exact
        PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup.operator_mem_vacuumOrthogonal
          (C.finitePhysicalSemigroup n) hSymmetric t
          (psi : Pn.PhysicalHilbert) psi.property⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

/-- Continuous finite Wilson transfer on the vacuum-orthogonal sector. -/
noncomputable def finiteVacuumOrthogonalTransfer
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert :=
  (finiteVacuumOrthogonalTransferLinearMap C hExchange n t).mkContinuous 1
    (by
      intro psi
      change
        ‖C.finiteOperator n t
            (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
              S D halfExtent N hN beta hbeta B hInvariant n)‖ ≤
          1 * ‖(psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
            S D halfExtent N hN beta hbeta B hInvariant n)‖
      calc
        ‖C.finiteOperator n t
            (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
              S D halfExtent N hN beta hbeta B hInvariant n)‖ ≤
          ‖C.finiteOperator n t‖ *
            ‖(psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
              S D halfExtent N hN beta hbeta B hInvariant n)‖ :=
          (C.finiteOperator n t).le_opNorm _
        _ ≤ 1 *
            ‖(psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
              S D halfExtent N hN beta hbeta B hInvariant n)‖ :=
          mul_le_mul_of_nonneg_right
            (C.finiteOperator_opNorm_le n t) (norm_nonneg _))

@[simp] theorem finiteVacuumOrthogonalTransfer_coe
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ((finiteVacuumOrthogonalTransfer C hExchange n t psi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n) =
      C.finiteOperator n t
        (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n) := by
  rfl

/-- The corrected canonical boundary excitation transfer intertwines exactly
with the finite vacuum-sector transfer, including the boundary half-time
convention. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_intertwining_restricted
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t
        (L.completedVacuumOrthogonalLinearIsometry n psi) =
      L.completedVacuumOrthogonalLinearIsometry n
        (finiteVacuumOrthogonalTransfer C hExchange n (t / 2) psi) := by
  apply Subtype.ext
  exact L.canonicalBoundaryVacuumOrthogonalTransfer_intertwining
    C hExchange n t psi

/-- The finite vacuum-sector operator norm is bounded above by the corrected
canonical boundary excitation operator norm.  This follows by testing the
boundary operator on the isometric physical image. -/
theorem finiteVacuumOrthogonalTransfer_opNorm_le_canonicalBoundary
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2)‖ ≤
      ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (ContinuousLinearMap.opNorm_nonneg
      (L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t)) ?_
  intro psi
  have hInter :=
    L.canonicalBoundaryVacuumOrthogonalTransfer_intertwining_restricted
      C hExchange n t psi
  calc
    ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2) psi‖ =
        ‖L.completedVacuumOrthogonalLinearIsometry n
          (finiteVacuumOrthogonalTransfer C hExchange n (t / 2) psi)‖ :=
      ((L.completedVacuumOrthogonalLinearIsometry n).norm_map _).symm
    _ = ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t
          (L.completedVacuumOrthogonalLinearIsometry n psi)‖ := by
      rw [hInter]
    _ ≤ ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t‖ *
        ‖L.completedVacuumOrthogonalLinearIsometry n psi‖ :=
      (L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t).le_opNorm _
    _ = ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t‖ * ‖psi‖ := by
      rw [(L.completedVacuumOrthogonalLinearIsometry n).norm_map]

/-- Conversely, the canonical boundary excitation operator norm cannot exceed
the finite vacuum-sector norm.  The boundary operator first applies the
coisometry `J†`, whose norm is at most one, then the finite excitation transfer,
and finally the isometry `J`. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_opNorm_le_finite
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t‖ ≤
      ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (ContinuousLinearMap.opNorm_nonneg
      (finiteVacuumOrthogonalTransfer C hExchange n (t / 2))) ?_
  intro v
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let J := L.completedLinearIsometry n
  let Jadj :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n :=
    (J.toContinuousLinearMap)†
  let psi : Pn.VacuumOrthogonalHilbert :=
    ⟨Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N), by
      dsimp [Jadj, J]
      exact L.completedLinearIsometry_adjoint_mem_vacuumOrthogonal
        n (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
        v.property⟩
  have hAdjNorm :
      ‖psi‖ ≤ ‖v‖ := by
    change
      ‖Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)‖ ≤
        ‖(v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)‖
    dsimp [Jadj, J]
    exact L.completedLinearIsometry_adjoint_norm_le n
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
  change
    ‖J (C.finiteOperator n (t / 2)
        (Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)))‖ ≤
      ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2)‖ * ‖v‖
  rw [J.norm_map]
  change
    ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2) psi‖ ≤
      ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2)‖ * ‖v‖
  exact
    (finiteVacuumOrthogonalTransfer C hExchange n (t / 2)).le_opNorm psi |>.trans
      (mul_le_mul_of_nonneg_left hAdjNorm (norm_nonneg _))

/-- Exact operator-norm identification: the corrected canonical boundary
excitation transfer contains no additional strict-contraction assumption.
Its norm is exactly the norm of the actual finite Wilson OS transfer on the
vacuum-orthogonal physical sector, at half the boundary time. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_opNorm_eq_finite
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t‖ =
      ‖finiteVacuumOrthogonalTransfer C hExchange n (t / 2)‖ := by
  apply le_antisymm
  · exact L.canonicalBoundaryVacuumOrthogonalTransfer_opNorm_le_finite
      C hExchange n t
  · exact L.finiteVacuumOrthogonalTransfer_opNorm_le_canonicalBoundary
      C hExchange n t

/-- At the boundary time `2t`, the exact operator norm is the physical finite
vacuum-sector norm at time `t`. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_opNorm_eq_finite_physicalTime
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal) :
    ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n (2 * t)‖ =
      ‖finiteVacuumOrthogonalTransfer C hExchange n t‖ := by
  rw [L.canonicalBoundaryVacuumOrthogonalTransfer_opNorm_eq_finite
    C hExchange n (2 * t)]
  congr 1
  ext
  norm_num

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end
