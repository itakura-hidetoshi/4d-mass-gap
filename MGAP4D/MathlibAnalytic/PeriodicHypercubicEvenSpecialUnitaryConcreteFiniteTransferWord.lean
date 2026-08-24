import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableInsertion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance concreteFiniteTransferWordSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance concreteFiniteTransferWordSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance concreteFiniteTransferWordSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance concreteFiniteTransferWordSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance concreteFiniteTransferWordSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance concreteFiniteTransferWordSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance concreteFiniteTransferWordSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual one-slice Haar Hilbert carrier used by finite transfer words. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The finite Gauss-law Hilbert sector on which gauge-invariant words act. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
    (H N : ℕ) : Type :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

/-- A concrete chronological letter for the finite transfer language.

`transfer` advances by one ordinary Wilson slab, `slice` inserts a bounded
one-slice observable without advancing the slab count, and `slab` inserts a
bounded adjacent-slice observable while advancing by one slab.  Gauge
invariance is stored with observable letters so every word has a genuine
physical Gauss-law realization. -/
inductive PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter
    (H N : ℕ) : Type where
  | transfer
  | slice
      (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
      (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
  | slab
      (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
      (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)

/-- A finite transfer word is a chronological list, read from the initial
boundary toward the final boundary. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord
    (H N : ℕ) : Type :=
  List (PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N)

/-- Number of actual transfer slabs consumed by one letter. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount
    {H N : ℕ} :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N → ℕ
  | .transfer => 1
  | .slice _ _ => 0
  | .slab _ _ => 1

/-- Total number of transfer slabs consumed by a chronological word. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
    {H N : ℕ} :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N → ℕ
  | [] => 0
  | letter :: word =>
      periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount letter +
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount word

/-- Slab count is additive under chronological concatenation. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append
    {H N : ℕ}
    (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount (u ++ v) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount u +
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount v := by
  induction u with
  | nil => rfl
  | cons letter u ih =>
      simp only [List.cons_append,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount]
      rw [ih]
      omega

/-- A chronological block of `n` ordinary transfer slabs. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock
    (H N : ℕ) : ℕ → PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N
  | 0 => []
  | n + 1 =>
      PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter.transfer ::
        periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n

/-- An ordinary transfer block consumes exactly its declared number of slabs. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock_slabCount
    (H N n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount, ih]

/-- Ambient Haar-`L²` operator represented by one transfer letter. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N :=
  match letter with
  | .transfer =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
  | .slice a _ =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
  | .slab b _ =>
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
        H N hN beta hbeta b

/-- Genuine Gauss-law operator represented by one gauge-invariant letter. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  match letter with
  | .transfer =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
  | .slice a ha =>
      periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
        H N a ha
  | .slab b hb =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
        H N hN beta hbeta b hb

/-- Forgetting the Gauss-law subtype turns each physical letter into its
ambient Haar-`L²` operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ((periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
        H N hN beta hbeta letter f :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
        H N hN beta hbeta letter
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  cases letter with
  | transfer =>
      exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
        H N hN beta hbeta f
  | slice a ha =>
      exact periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_coe
        H N a ha f
  | slab b hb =>
      exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_coe
        H N hN beta hbeta b hb f

/-- Ambient operator of a chronological word.  The first list letter acts
first on the initial state, hence the recursive tail composes on the left. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N →
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
  | [] =>
      ContinuousLinearMap.id ℝ
        (PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
  | letter :: word =>
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta word).comp
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
          H N hN beta hbeta letter)

/-- Physical Gauss-law operator of a chronological finite word. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N →
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
  | [] =>
      ContinuousLinearMap.id ℝ
        (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
  | letter :: word =>
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta word).comp
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
          H N hN beta hbeta letter)

/-- Concatenating chronological physical words means applying the first word
and then the second word. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta (u ++ v) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta v
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta u f) := by
  induction u generalizing f with
  | nil => rfl
  | cons letter u ih =>
      change
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta (u ++ v)
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
              H N hN beta hbeta letter f) =
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta v
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
              H N hN beta hbeta u
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
                H N hN beta hbeta letter f))
      exact ih
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
          H N hN beta hbeta letter f)

/-- The same concatenation law on ambient Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator_append_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
        H N hN beta hbeta (u ++ v) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
        H N hN beta hbeta v
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta u f) := by
  induction u generalizing f with
  | nil => rfl
  | cons letter u ih =>
      change
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
            H N hN beta hbeta (u ++ v)
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
              H N hN beta hbeta letter f) =
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
            H N hN beta hbeta v
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
              H N hN beta hbeta u
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
                H N hN beta hbeta letter f))
      exact ih
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
          H N hN beta hbeta letter f)

/-- Word evaluation commutes with forgetting the Gauss-law subtype. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta word f :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
        H N hN beta hbeta word
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  induction word generalizing f with
  | nil => rfl
  | cons letter word ih =>
      change
        ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta word
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
              H N hN beta hbeta letter f) :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta word
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
            H N hN beta hbeta letter
            (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N))
      rw [ih]
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator_coe]

/-- A transfer block evaluates to the corresponding physical transfer power. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n) f =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ n) f := by
  induction n generalizing f with
  | zero =>
      simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator]
  | succ n ih =>
      change
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta f) =
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ Nat.succ n) f
      simpa [pow_succ, ContinuousLinearMap.mul_def] using
        ih (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f)

/-- A transfer block evaluates to the corresponding ambient transfer power. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockAmbientOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n) f =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta) ^ n) f := by
  induction n generalizing f with
  | zero =>
      simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator]
  | succ n ih =>
      change
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n)
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
              H N hN beta hbeta f) =
          ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H N hN beta hbeta) ^ Nat.succ n) f
      simpa [pow_succ, ContinuousLinearMap.mul_def] using
        ih (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f)

/-- Word with one bounded one-slice insertion between ordinary transfer blocks. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
    (H N : ℕ)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
    [PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter.slice a ha] ++
      periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right

/-- Word with one bounded adjacent-slice insertion between ordinary transfer blocks. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
    (H N : ℕ)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
    [PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter.slab b hb] ++
      periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right

/-- A one-slice insertion word consumes only its ordinary transfer blocks. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_slabCount
    (H N left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
          H N left right a ha) = left + right := by
  simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock_slabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount]

/-- An adjacent-slice insertion word consumes the inserted slab as well. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_slabCount
    (H N left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
          H N left right b hb) = left + right + 1 := by
  simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock_slabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount]
  omega

/-- The one-slice insertion word is exactly the previously constructed
physical operator `T^right M_a T^left`. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
          H N left right a ha) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
        H N hN beta hbeta left right a ha := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
          H N left right a ha) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right)
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          [PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter.slice a ha]
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left) f)) := by
      unfold periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
    _ = ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ right)
          (periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
            H N a ha
            (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta) ^ left) f)) := by
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
      rfl
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
        H N hN beta hbeta left right a ha f := by
      rfl

/-- The adjacent-slice insertion word is exactly the previously constructed
physical operator `T^right T_b T^left`. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
          H N left right b hb) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
        H N hN beta hbeta left right b hb := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
          H N left right b hb) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right)
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          [PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter.slab b hb]
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left) f)) := by
      unfold periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
    _ = ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ right)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
            H N hN beta hbeta b hb
            (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta) ^ left) f)) := by
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
      rfl
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
        H N hN beta hbeta left right b hb f := by
      rfl

/-- Matrix coefficients of a one-slice word retain the literal finite Haar
path amplitude already proved for arbitrary transfer slices. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_inner_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
            H N left right a ha) f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude
        H N beta left right a
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_inner_eq_amplitude
      H N hN beta hbeta left right a ha f g

/-- Matrix coefficients of an adjacent-slice word retain the literal finite
Haar path amplitude proved for arbitrary transfer slabs. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_inner_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
            H N left right b hb) f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude
        H N beta left right b
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_inner_eq_amplitude
      H N hN beta hbeta left right b hb f g

/-- Concrete chronological word for the actual spatial Wilson action at one
slice. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord
    (H N left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
    H N left right
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
      H N)

/-- Concrete chronological word for the actual temporal crossing Wilson
action on one slab. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord
    (H N left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
    H N left right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
      H N)

/-- The spatial Wilson word evaluates to the concrete arbitrary-slice Wilson
operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWordPhysicalOperator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord
          H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
        H N hN beta hbeta left right := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord,
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator] using
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq
        H N hN beta hbeta left right
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
          H N))

/-- The temporal crossing word evaluates to the concrete arbitrary-slab Wilson
operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWordPhysicalOperator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord
          H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
        H N hN beta hbeta left right := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord,
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator] using
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
        H N hN beta hbeta left right
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant
          H N))

/-- Audit-visible receipt that the finite chronological language is a genuine
physical operator language and that both single-generator insertion bridges
are recovered by its evaluator. -/
structure PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  physicalToAmbient :
    ∀ (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N),
      ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta word f :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta word
          (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
  sliceInsertion :
    ∀ (left right : ℕ)
      (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
      (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a),
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
            H N left right a ha) =
        periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
          H N hN beta hbeta left right a ha
  slabInsertion :
    ∀ (left right : ℕ)
      (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
      (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b),
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
            H N left right b hb) =
        periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
          H N hN beta hbeta left right b hb
  spatialWilson :
    ∀ left right : ℕ,
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord
            H N left right) =
        periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
          H N hN beta hbeta left right
  temporalCrossing :
    ∀ left right : ℕ,
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord
            H N left right) =
        periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
          H N hN beta hbeta left right

/-- Construct the finite chronological transfer-word receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage
      H N hN beta hbeta :=
  { physicalToAmbient :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_coe
        H N hN beta hbeta
    sliceInsertion :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq
        H N hN beta hbeta
    slabInsertion :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
        H N hN beta hbeta
    spatialWilson :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWordPhysicalOperator_eq
        H N hN beta hbeta
    temporalCrossing :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWordPhysicalOperator_eq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
