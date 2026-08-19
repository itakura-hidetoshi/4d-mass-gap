import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitCompletionContraction
import Mathlib.Tactic

/-!
# Rational-time semigroup coherence on the completed factorial OS direct limit

The preceding layers construct, for every nonnegative rational time `t`, a canonical contraction on
both the algebraic direct limit of finite-slot primary-scalar OS Hilbert sectors and its Mathlib
completion.  This file proves the exact zero and additive coherence laws for those operators.

The only subtlety is dependent finite-slot bookkeeping.  Two successive translations and one
translation by the summed time land in canonically equivalent slot sets, but their proof fields need
not be definitionally identical.  We therefore do not cast between those Hilbert sectors.  Instead,
we insert both translated vectors isometrically into one finite common upper sector and compare them
there.  On the dense carrier the equality is exactly the already-canonical full-path observable
coherence; quotient and Hilbert completion then preserve it.  The algebraic direct-limit law follows
representative-wise, and the completed law follows by density and continuity.

Thus the completed contractions satisfy

`T_0 = id` and `T_s (T_t x) = T_(t+s) x`

for all nonnegative rational `s,t`.  No real-time extension, strong continuity, generator,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

noncomputable section

/-- Pullback of a finite-slot bounded-continuous observable to the full rational path is injective.
Every finite coordinate assignment extends to a full path, so equality after pullback determines the
original cylinder observable exactly. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_injective
    (J : Finset ℚ) :
    Function.Injective
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J) := by
  intro F G hFG
  ext v
  let x : ℚ → ℝ := fun q => if hq : q ∈ J then v ⟨q, hq⟩ else 0
  have hEval :=
    congrArg
      (fun K : BoundedContinuousFunction (ℚ → ℝ) ℝ => K x)
      hFG
  change F (fun q : J => x q.1) = G (fun q : J => x q.1) at hEval
  have hx : (fun q : J => x q.1) = v := by
    funext q
    simp [x, q.2]
  simpa [hx] using hEval

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Zero-time translation and the original carrier vector agree after inserting both into any
common finite-slot upper sector. -/
theorem fixedSlotIndexedCarrierTimeTranslate_zero_common
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J M : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h0 : primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J ≤ M)
    (hJ : J ≤ M)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J)).fixedSlotCarrierInclusion
        (P.fixedSlotDataOfIndex M) h0
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate 0 le_rfl F) =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierInclusion
        (P.fixedSlotDataOfIndex M) hJ F := by
  apply FixedSlotCarrier.observable_injective (P.fixedSlotDataOfIndex M)
  apply
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_injective
      M.1
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable M.1
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
            0 J.1)
          M.1 h0
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J.1 0 F.observable)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable M.1
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J.1 M.1 hJ F.observable)
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate
        J.1 0 F.observable =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        J.1 F.observable
  simpa using
    congrArg
      (fun A => A F.observable)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate_zero
        J.1)

/-- Two successive nonnegative rational translations and one translation by their sum agree after
inserting both outputs into any common finite-slot upper sector. -/
theorem fixedSlotIndexedCarrierTimeTranslate_add_common
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J M : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hst :
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J) ≤ M)
    (hsum :
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J ≤ M)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J))).fixedSlotCarrierInclusion
        (P.fixedSlotDataOfIndex M) hst
        ((P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotCarrierTimeTranslate
          s hs
          ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate t ht F)) =
      (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J)).fixedSlotCarrierInclusion
        (P.fixedSlotDataOfIndex M) hsum
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate
          (t + s) (add_nonneg ht hs) F) := by
  apply FixedSlotCarrier.observable_injective (P.fixedSlotDataOfIndex M)
  apply
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_injective
      M.1
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable M.1
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate s
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
              t J.1))
          M.1 hst
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
              t J.1)
            s
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
              J.1 t F.observable))) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable M.1
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
            (t + s) J.1)
          M.1 hsum
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J.1 (t + s) F.observable))
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate_add
      J.1 t s F.observable

/-- Zero-time Hilbert translation agrees with the original vector after canonical insertion into a
common indexed Hilbert sector. -/
theorem fixedSlotIndexedHilbertTimeTranslate_zero_common
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J M : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h0 : primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J ≤ M)
    (hJ : J ≤ M)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotIndexedHilbertMap
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J) M h0
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl x) =
      P.fixedSlotIndexedHilbertMap J M hJ x := by
  change
    (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J)).fixedSlotHilbertInclusion
        (P.fixedSlotDataOfIndex M) h0
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl x) =
      (P.fixedSlotDataOfIndex J).fixedSlotHilbertInclusion
        (P.fixedSlotDataOfIndex M) hJ x
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_eq
          (((P.fixedSlotDataOfIndex
              (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J)).fixedSlotHilbertLinearIsometry
              (P.fixedSlotDataOfIndex M) h0).continuous.comp
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl).continuous)
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertLinearIsometry
            (P.fixedSlotDataOfIndex M) hJ).continuous
  | ih x =>
      obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
      change
        (P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J)).fixedSlotHilbertInclusion
            (P.fixedSlotDataOfIndex M) h0
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl
              ((P.fixedSlotDataOfIndex J).hilbertState F)) =
          (P.fixedSlotDataOfIndex J).fixedSlotHilbertInclusion
            (P.fixedSlotDataOfIndex M) hJ
            ((P.fixedSlotDataOfIndex J).hilbertState F)
      rw [(P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM_hilbertState]
      rw [(P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J)).fixedSlotHilbertInclusion_hilbertState]
      rw [(P.fixedSlotDataOfIndex J).fixedSlotHilbertInclusion_hilbertState]
      rw [P.fixedSlotIndexedCarrierTimeTranslate_zero_common J M h0 hJ F]

/-- Additive rational-time Hilbert coherence after canonical insertion into any common upper
finite-slot sector. -/
theorem fixedSlotIndexedHilbertTimeTranslate_add_common
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J M : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hst :
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J) ≤ M)
    (hsum :
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J ≤ M)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotIndexedHilbertMap
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)) M hst
        ((P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertTimeTranslateCLM
          s hs
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)) =
      P.fixedSlotIndexedHilbertMap
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J) M hsum
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
          (t + s) (add_nonneg ht hs) x) := by
  change
    (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J))).fixedSlotHilbertInclusion
        (P.fixedSlotDataOfIndex M) hst
        ((P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertTimeTranslateCLM
          s hs
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)) =
      (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J)).fixedSlotHilbertInclusion
        (P.fixedSlotDataOfIndex M) hsum
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
          (t + s) (add_nonneg ht hs) x)
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_eq
          (((P.fixedSlotDataOfIndex
              (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
                (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J))).fixedSlotHilbertLinearIsometry
              (P.fixedSlotDataOfIndex M) hst).continuous.comp
            (((P.fixedSlotDataOfIndex
                (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertTimeTranslateCLM
                s hs).continuous.comp
              ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht).continuous))
          (((P.fixedSlotDataOfIndex
              (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
                (t + s) (add_nonneg ht hs) J)).fixedSlotHilbertLinearIsometry
              (P.fixedSlotDataOfIndex M) hsum).continuous.comp
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
              (t + s) (add_nonneg ht hs)).continuous)
  | ih x =>
      obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
      change
        (P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
              (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J))).fixedSlotHilbertInclusion
            (P.fixedSlotDataOfIndex M) hst
            ((P.fixedSlotDataOfIndex
                (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertTimeTranslateCLM
              s hs
              ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht
                ((P.fixedSlotDataOfIndex J).hilbertState F))) =
          (P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
              (t + s) (add_nonneg ht hs) J)).fixedSlotHilbertInclusion
            (P.fixedSlotDataOfIndex M) hsum
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
              (t + s) (add_nonneg ht hs)
              ((P.fixedSlotDataOfIndex J).hilbertState F))
      rw [(P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM_hilbertState]
      rw [(P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertTimeTranslateCLM_hilbertState]
      rw [(P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J))).fixedSlotHilbertInclusion_hilbertState]
      rw [(P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM_hilbertState]
      rw [(P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
          (t + s) (add_nonneg ht hs) J)).fixedSlotHilbertInclusion_hilbertState]
      rw [P.fixedSlotIndexedCarrierTimeTranslate_add_common J M t s ht hs hst hsum F]

/-- Zero rational time acts identically on the algebraic Hilbert direct limit. -/
@[simp]
theorem fixedSlotHilbertAlgebraicTimeTranslate_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicTimeTranslate 0 le_rfl z = z := by
  obtain ⟨J, x, rfl⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  let J0 : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J
  let M : PrimaryScalarFiniteNonnegativeSlotIndex :=
    ⟨J0.1 ∪ J.1, by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact J0.2 q hq
      · exact J.2 q hq⟩
  have h0 : J0 ≤ M := Finset.subset_union_left
  have hJ : J ≤ M := Finset.subset_union_right
  change
    P.fixedSlotHilbertAlgebraicOf J0
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl x) =
      P.fixedSlotHilbertAlgebraicOf J x
  calc
    P.fixedSlotHilbertAlgebraicOf J0
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl x) =
      P.fixedSlotHilbertAlgebraicOf M
        (P.fixedSlotIndexedHilbertMap J0 M h0
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM 0 le_rfl x)) := by
        symm
        exact P.fixedSlotHilbertAlgebraicOf_map J0 M h0 _
    _ = P.fixedSlotHilbertAlgebraicOf M
        (P.fixedSlotIndexedHilbertMap J M hJ x) := by
      exact congrArg (P.fixedSlotHilbertAlgebraicOf M)
        (P.fixedSlotIndexedHilbertTimeTranslate_zero_common J M h0 hJ x)
    _ = P.fixedSlotHilbertAlgebraicOf J x :=
      P.fixedSlotHilbertAlgebraicOf_map J M hJ x

/-- Composing algebraic direct-limit translations first by `t` and then by `s` is exactly
translation by `t+s`. -/
theorem fixedSlotHilbertAlgebraicTimeTranslate_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicTimeTranslate s hs
        (P.fixedSlotHilbertAlgebraicTimeTranslate t ht z) =
      P.fixedSlotHilbertAlgebraicTimeTranslate
        (t + s) (add_nonneg ht hs) z := by
  obtain ⟨J, x, rfl⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  let Jt : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J
  let Jst : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs Jt
  let Jsum : PrimaryScalarFiniteNonnegativeSlotIndex :=
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate (t + s) (add_nonneg ht hs) J
  let M : PrimaryScalarFiniteNonnegativeSlotIndex :=
    ⟨Jst.1 ∪ Jsum.1, by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact Jst.2 q hq
      · exact Jsum.2 q hq⟩
  have hst : Jst ≤ M := Finset.subset_union_left
  have hsum : Jsum ≤ M := Finset.subset_union_right
  change
    P.fixedSlotHilbertAlgebraicOf Jst
        ((P.fixedSlotDataOfIndex Jt).fixedSlotHilbertTimeTranslateCLM s hs
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)) =
      P.fixedSlotHilbertAlgebraicOf Jsum
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
          (t + s) (add_nonneg ht hs) x)
  calc
    P.fixedSlotHilbertAlgebraicOf Jst
        ((P.fixedSlotDataOfIndex Jt).fixedSlotHilbertTimeTranslateCLM s hs
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)) =
      P.fixedSlotHilbertAlgebraicOf M
        (P.fixedSlotIndexedHilbertMap Jst M hst
          ((P.fixedSlotDataOfIndex Jt).fixedSlotHilbertTimeTranslateCLM s hs
            ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x))) := by
      symm
      exact P.fixedSlotHilbertAlgebraicOf_map Jst M hst _
    _ = P.fixedSlotHilbertAlgebraicOf M
        (P.fixedSlotIndexedHilbertMap Jsum M hsum
          ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
            (t + s) (add_nonneg ht hs) x)) := by
      exact congrArg (P.fixedSlotHilbertAlgebraicOf M)
        (P.fixedSlotIndexedHilbertTimeTranslate_add_common
          J M t s ht hs hst hsum x)
    _ = P.fixedSlotHilbertAlgebraicOf Jsum
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM
          (t + s) (add_nonneg ht hs) x) :=
      P.fixedSlotHilbertAlgebraicOf_map Jsum M hsum _

/-- Continuous-linear algebraic direct-limit translation at zero is the identity. -/
@[simp]
theorem fixedSlotHilbertAlgebraicTimeTranslateCLM_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertAlgebraicTimeTranslateCLM 0 le_rfl =
      ContinuousLinearMap.id ℝ P.fixedSlotHilbertAlgebraicDirectLimit := by
  ext z
  change P.fixedSlotHilbertAlgebraicTimeTranslate 0 le_rfl z = z
  exact P.fixedSlotHilbertAlgebraicTimeTranslate_zero z

/-- The algebraic direct-limit continuous contractions compose with additive rational time. -/
theorem fixedSlotHilbertAlgebraicTimeTranslateCLM_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (P.fixedSlotHilbertAlgebraicTimeTranslateCLM s hs).comp
        (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht) =
      P.fixedSlotHilbertAlgebraicTimeTranslateCLM
        (t + s) (add_nonneg ht hs) := by
  ext z
  change
    P.fixedSlotHilbertAlgebraicTimeTranslate s hs
        (P.fixedSlotHilbertAlgebraicTimeTranslate t ht z) =
      P.fixedSlotHilbertAlgebraicTimeTranslate
        (t + s) (add_nonneg ht hs) z
  exact P.fixedSlotHilbertAlgebraicTimeTranslate_add t s ht hs z

/-- Zero rational time acts identically on the completed direct-limit carrier. -/
@[simp]
theorem fixedSlotHilbertDirectLimitTimeTranslate_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM 0 le_rfl x = x := by
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_eq
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM 0 le_rfl).continuous
          continuous_id
  | ih z =>
      rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
      change
        (P.fixedSlotHilbertAlgebraicTimeTranslate 0 le_rfl z :
          Completion P.fixedSlotHilbertAlgebraicDirectLimit) =
        (z : Completion P.fixedSlotHilbertAlgebraicDirectLimit)
      rw [P.fixedSlotHilbertAlgebraicTimeTranslate_zero]

/-- Completed direct-limit contractions satisfy the exact nonnegative-rational semigroup law. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM s hs
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x) =
      P.fixedSlotHilbertDirectLimitTimeTranslateCLM
        (t + s) (add_nonneg ht hs) x := by
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_eq
          ((P.fixedSlotHilbertDirectLimitTimeTranslateCLM s hs).continuous.comp
            (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht).continuous)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (t + s) (add_nonneg ht hs)).continuous
  | ih z =>
      rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
      rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
      rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
      change
        (P.fixedSlotHilbertAlgebraicTimeTranslate s hs
            (P.fixedSlotHilbertAlgebraicTimeTranslate t ht z) :
          Completion P.fixedSlotHilbertAlgebraicDirectLimit) =
        (P.fixedSlotHilbertAlgebraicTimeTranslate
            (t + s) (add_nonneg ht hs) z :
          Completion P.fixedSlotHilbertAlgebraicDirectLimit)
      rw [P.fixedSlotHilbertAlgebraicTimeTranslate_add]

/-- Completed time translation at zero is the identity continuous linear map. -/
@[simp]
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM 0 le_rfl =
      ContinuousLinearMap.id ℝ P.fixedSlotHilbertDirectLimitCompletion := by
  ext x
  exact P.fixedSlotHilbertDirectLimitTimeTranslate_zero x

/-- The completed contractions compose exactly according to addition of nonnegative rational time. -/
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (P.fixedSlotHilbertDirectLimitTimeTranslateCLM s hs).comp
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht) =
      P.fixedSlotHilbertDirectLimitTimeTranslateCLM
        (t + s) (add_nonneg ht hs) := by
  ext x
  exact P.fixedSlotHilbertDirectLimitTimeTranslate_add t s ht hs x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D