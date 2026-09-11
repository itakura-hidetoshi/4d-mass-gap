import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteTranslatedMeanSubtractedReflectionLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalSmoothedCarrierCore
import Mathlib.Tactic

/-!
# Finite Wilson centered reflection forms on the smoothed literal excitation core

The preceding same-root layers now provide both sides of the quantitative interface needed for a
future positive mass estimate:

* literal finite Wilson translated reflection forms centered by their own translated finite means;
* a dense exact excitation core obtained by centering positive-time translates of literal
  bounded-continuous fixed-slot cylinders.

This file identifies those two constructions directly.

For a literal cylinder `F` and positive smoothing time `s`, the exact dense-core vector is

`T_s (x_F - <Omega,x_F> Omega)`.

We prove that this is exactly the regular centering of the positive-time-smoothed literal carrier
used by the existing dense-core theorem.  We then package the actual finite Wilson quantity at
shift `s+h`,

`R_n(F;s,h) = Q_n(tau_(s+h) F) - E_n[tau_(s+h) F]^2`,

and prove

`R_n(F;s,h) -> <T_s x_F^o, T_(2h) T_s x_F^o>`.

At `h=0` the same finite quantity converges to `||T_s x_F^o||^2`.  Thus a future scale-uniform
finite estimate can be stated with exactly the numerator and denominator corresponding to the
already-dense same-root excitation core, without changing centering conventions or carriers.

No decay estimate, positive lower bound, non-collapse theorem, positive `m_OS`, spectral gap,
old-carrier equivalence, or heat-bath/physical-time identification is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology UniformSpace
open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Canonical positive-time-smoothed literal carrier as an element of the already-defined
smoothed-carrier set. -/
noncomputable def fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierOf
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierSet :=
  ⟨P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
      (P.fixedSlotHilbertDirectLimitCarrierState J F),
    ⟨s, hs, J, F, rfl⟩⟩

/-- Explicit centered positive-time-smoothed literal state in the completed same-root Hilbert
carrier. -/
noncomputable def fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitCompletion :=
  P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
    (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)

/-- Positive smoothing puts the explicitly centered literal state in the canonical regular sector. -/
theorem fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState_mem_regularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F ∈
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  exact
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos
      s hs (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)

/-- The explicitly smoothed-centered literal state remains exactly vacuum-orthogonal. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuum_inner_smoothedCenteredCarrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F) = 0 := by
  have hsym :=
    P.fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
      (s : ℚ) s.2 P.fixedSlotHilbertDirectLimitVacuum
      (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
  have hvac :
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          P.fixedSlotHilbertDirectLimitVacuum =
        P.fixedSlotHilbertDirectLimitVacuum := by
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using
      P.fixedSlotHilbertDirectLimitTimeTranslateCLM_vacuum (s : ℚ) s.2
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          P.fixedSlotHilbertDirectLimitVacuum)
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F) := by
          simpa [fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState,
            fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using hsym.symm
    _ = inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F) := by rw [hvac]
    _ = 0 :=
      P.fixedSlotHilbertDirectLimitVacuum_inner_centeredCarrierState J F

/-- Exact commutation of probabilistic/Hilbert centering with positive rational smoothing for a
literal carrier.  This identifies the explicit `T_s x_F^o` state with the centering operation used
by the pre-existing dense excitation-core construction. -/
theorem fixedSlotHilbertDirectLimitRegularCentered_positiveTimeSmoothedCarrierOf_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ((P.fixedSlotHilbertDirectLimitRegularCentered
        (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierRegular
          (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierOf J s hs F)) :
        P.fixedSlotHilbertDirectLimitRegularSubspace) :
      P.fixedSlotHilbertDirectLimitCompletion) =
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F := by
  let μ := (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F
  have hmean :
      inner ℝ P.fixedSlotHilbertDirectLimitVacuum
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (P.fixedSlotHilbertDirectLimitCarrierState J F)) = μ := by
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM, μ] using
      P.fixedSlotHilbertDirectLimitVacuum_inner_timeTranslate_carrierState_eq_continuumMean
        J (s : ℚ) s.2 F
  have hvac :
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          P.fixedSlotHilbertDirectLimitVacuum =
        P.fixedSlotHilbertDirectLimitVacuum := by
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using
      P.fixedSlotHilbertDirectLimitTimeTranslateCLM_vacuum (s : ℚ) s.2
  change
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (P.fixedSlotHilbertDirectLimitCarrierState J F) -
        inner ℝ P.fixedSlotHilbertDirectLimitVacuum
            (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
              (P.fixedSlotHilbertDirectLimitCarrierState J F)) •
          P.fixedSlotHilbertDirectLimitVacuum =
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (P.fixedSlotHilbertDirectLimitCarrierState J F -
          μ • P.fixedSlotHilbertDirectLimitVacuum)
  rw [hmean, map_sub, map_smul, hvac]

/-- The explicit positive-time-smoothed centered state, corestricted to the canonical regular
vacuum-orthogonal Hilbert carrier. -/
noncomputable def fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  ⟨⟨P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F,
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState_mem_regularSubspace J s hs F⟩,
    by
      rw [P.mem_fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_iff]
      change
        inner ℝ P.fixedSlotHilbertDirectLimitVacuum
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F) = 0
      exact P.fixedSlotHilbertDirectLimitVacuum_inner_smoothedCenteredCarrierState J s F⟩

/-- The explicit smoothed-centered excitation is exactly the already-canonical centered
positive-time-smoothed literal carrier excitation. -/
theorem fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation_of_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation
        (P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierOf J s hs F) =
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation J s hs F := by
  apply Subtype.ext
  apply Subtype.ext
  exact
    P.fixedSlotHilbertDirectLimitRegularCentered_positiveTimeSmoothedCarrierOf_coe J s hs F

/-- Explicit parameterization of the dense centered literal excitation family. -/
def fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
  {ξ | ∃ s : NNRat, ∃ hs : 0 < s,
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
        ξ = P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation J s hs F}

/-- The previously proved dense carrier core is contained in the explicit `T_s x_F^o`
parameterization. -/
theorem fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet_subset_explicit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet ⊆
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet := by
  rintro ξ ⟨y, rfl⟩
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨s, hs, J, F, rfl⟩
  refine ⟨s, hs, J, F, ?_⟩
  simpa [fixedSlotHilbertDirectLimitPositiveTimeSmoothedCarrierOf] using
    P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitation_of_eq J s hs F

/-- Therefore the explicitly parameterized smoothed-centered literal family itself has full
closure in the exact same-root excitation Hilbert carrier. -/
theorem fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet_closure_eq_univ
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    closure P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ξ
  have hx :
      ξ ∈ closure
        P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mem_closure_centeredSmoothedCarrier ξ
  exact
    (closure_mono
      P.fixedSlotHilbertDirectLimitCenteredPositiveTimeSmoothedCarrierExcitationSet_subset_explicit) hx

/-- Correlation identity that moves the smoothing time from the finite shift into the dense-core
state.  It is only symmetry plus the exact rational semigroup law. -/
theorem fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState_correlation_eq_shifted
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (((s : ℚ) + h) + ((s : ℚ) + h))
          (add_nonneg (add_nonneg s.2 hh) (add_nonneg s.2 hh))
          (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)) := by
  let x := P.fixedSlotHilbertDirectLimitCenteredCarrierState J F
  change
    inner ℝ
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM (s : ℚ) s.2 x)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM (s : ℚ) s.2 x)) =
      inner ℝ x
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (((s : ℚ) + h) + ((s : ℚ) + h))
          (add_nonneg (add_nonneg s.2 hh) (add_nonneg s.2 hh)) x)
  rw [P.fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
    (s : ℚ) s.2 x
    (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
      (h + h) (add_nonneg hh hh)
      (P.fixedSlotHilbertDirectLimitTimeTranslateCLM (s : ℚ) s.2 x))]
  rw [P.fixedSlotHilbertDirectLimitTimeTranslate_add
    (s : ℚ) (h + h) s.2 (add_nonneg hh hh) x]
  rw [P.fixedSlotHilbertDirectLimitTimeTranslate_add
    ((s : ℚ) + (h + h)) (s : ℚ)
    (add_nonneg s.2 (add_nonneg hh hh)) s.2 x]
  congr 2
  ring

/-- Actual finite Wilson centered reflection quantity aligned with a positive smoothing time `s`
and a subsequent correlation time `h`. -/
noncomputable def fixedSlotCarrierFiniteSmoothedCenteredReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm
    J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- Main dense-core finite-to-Hilbert receipt:

`Q_n(tau_(s+h) F) - E_n[tau_(s+h) F]^2`

converges to the exact smoothed centered correlation

`<T_s x_F^o, T_(2h) T_s x_F^o>`.
-/
theorem fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_correlation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n => P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n)
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)))) := by
  have hlim :=
    P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_tendsto_centeredCorrelation
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F
  simpa [fixedSlotCarrierFiniteSmoothedCenteredReflectionForm,
    P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState_correlation_eq_shifted J s h hh F]
    using hlim

/-- At zero subsequent separation, the same actual finite Wilson quantity converges to the squared
norm of the positive-time-smoothed centered dense-core state. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n => P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n)
      atTop
      (nhds (‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2)) := by
  have h :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_correlation
      J s 0 le_rfl F
  simpa [real_inner_self_eq_norm_sq] using h

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
