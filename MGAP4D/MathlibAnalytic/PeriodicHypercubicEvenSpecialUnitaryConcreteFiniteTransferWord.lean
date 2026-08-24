import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableInsertion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance concreteFiniteTransferWordSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance concreteFiniteTransferWordSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance concreteFiniteTransferWordSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupIsTopologicalGroup N
local instance concreteFiniteTransferWordSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupCompactSpace N
local instance concreteFiniteTransferWordSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupSecondCountableTopology N
local instance concreteFiniteTransferWordSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupMeasurableSpace N
local instance concreteFiniteTransferWordSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupBorelSpace N

abbrev PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert (H N : ℕ) : Type :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

/-- Concrete chronological letters: ordinary transfer, one-slice insertion,
or one adjacent-slice insertion. Observable letters carry gauge invariance so
every word has a genuine Gauss-law realization. -/
inductive PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter (H N : ℕ) : Type where
  | transfer
  | slice (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
      (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
  | slab (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
      (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)

abbrev PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord (H N : ℕ) : Type :=
  List (PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N)

def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount {H N : ℕ} :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N → ℕ
  | .transfer => 1
  | .slice _ _ => 0
  | .slab _ _ => 1

def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount {H N : ℕ} :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N → ℕ
  | [] => 0
  | x :: xs => periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount x +
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount xs

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append
    {H N : ℕ} (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount (u ++ v) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount u +
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount v := by
  induction u with
  | nil => simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount]
  | cons x xs ih =>
      simp only [List.cons_append, periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount]
      rw [ih]
      omega

def periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock
    (H N : ℕ) : ℕ → PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N
  | 0 => []
  | n + 1 => .transfer :: periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n

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
      omega

noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N :=
  match letter with
  | .transfer => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta
  | .slice a _ => periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a
  | .slab b _ => periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
      H N hN beta hbeta b

noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  match letter with
  | .transfer => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  | .slice a ha => periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator H N a ha
  | .slab b hb => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator
      H N hN beta hbeta b hb

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator_coe
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (letter : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferLetter H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ((periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
        H N hN beta hbeta letter f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
        H N hN beta hbeta letter (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  cases letter with
  | transfer => exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
      H N hN beta hbeta f
  | slice a ha => exact periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_coe
      H N a ha f
  | slab b hb => exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairObservableOperator_coe
      H N hN beta hbeta b hb f

noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N :=
  match word with
  | [] => ContinuousLinearMap.id ℝ _
  | letter :: tail =>
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
        H N hN beta hbeta tail).comp
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator
        H N hN beta hbeta letter)

noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  match word with
  | [] => ContinuousLinearMap.id ℝ _
  | letter :: tail =>
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta tail).comp
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator
        H N hN beta hbeta letter)

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta (u ++ v) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta v
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta u f) := by
  induction u generalizing f with
  | nil => rfl
  | cons letter u ih =>
      change periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta (u ++ v)
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator H N hN beta hbeta letter f) = _
      exact ih _

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator_append_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta (u ++ v) f =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta v
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta u f) := by
  induction u generalizing f with
  | nil => rfl
  | cons letter u ih =>
      change periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta (u ++ v)
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterAmbientOperator H N hN beta hbeta letter f) = _
      exact ih _

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_coe
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta word f :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta word
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  induction word generalizing f with
  | nil => rfl
  | cons letter word ih =>
      change ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta word
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator H N hN beta hbeta letter f) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) = _
      rw [ih, periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterPhysicalOperator_coe]

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n) f =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta) ^ n) f := by
  induction n generalizing f with
  | zero => simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock,
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator]
  | succ n ih =>
      change periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta f) = _
      simpa [pow_succ, ContinuousLinearMap.mul_def] using ih
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta f)

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockAmbientOperator_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n) f =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator H N hN beta hbeta) ^ n) f := by
  induction n generalizing f with
  | zero => simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock,
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator]
  | succ n ih =>
      change periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N n)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator H N hN beta hbeta f) = _
      simpa [pow_succ, ContinuousLinearMap.mul_def] using ih
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator H N hN beta hbeta f)

def periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord
    (H N left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
    [.slice a ha] ++ periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right

def periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
    (H N left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
    [.slab b hb] ++ periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_slabCount
    (H N left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha) = left + right := by
  simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock_slabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount]

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_slabCount
    (H N left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb) = left + right + 1 := by
  simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount_append,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock_slabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount]
  omega

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
        H N hN beta hbeta left right a ha := by
  apply ContinuousLinearMap.ext
  intro f
  rw [show periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
        ([.slice a ha] ++ periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right) by rfl]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
  rfl

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
        H N hN beta hbeta left right b hb := by
  apply ContinuousLinearMap.ext
  intro f
  rw [show periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N left ++
        ([.slab b hb] ++ periodicHypercubicEvenSpecialUnitaryFiniteTransferBlock H N right) by rfl]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_append_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferBlockPhysicalOperator_apply]
  rfl

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_inner_eq_amplitude
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha) f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude H N beta left right a
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator_inner_eq_amplitude
    H N hN beta hbeta left right a ha f g

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_inner_eq_amplitude
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb) f) g =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude H N beta left right b
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator_inner_eq_amplitude
    H N hN beta hbeta left right b hb f g

def periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord (H N left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant H N)

def periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord (H N left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant H N)

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWordPhysicalOperator_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
        H N hN beta hbeta left right := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord,
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator] using
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq
      H N hN beta hbeta left right
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant H N))

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWordPhysicalOperator_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
        H N hN beta hbeta left right := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord,
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator] using
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
      H N hN beta hbeta left right
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingActionBoundedPairObservable_gaugeInvariant H N))

structure PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  physicalToAmbient : ∀ (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N),
    ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta word f :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator H N hN beta hbeta word
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
  sliceInsertion : ∀ (left right : ℕ)
      (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
      (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a),
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceObservableOperator
        H N hN beta hbeta left right a ha
  slabInsertion : ∀ (left right : ℕ)
      (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
      (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b),
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
        H N hN beta hbeta left right b hb
  spatialWilson : ∀ left right : ℕ,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWord H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSliceSpatialWilsonActionOperator
        H N hN beta hbeta left right
  temporalCrossing : ∀ left right : ℕ,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWord H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabTemporalCrossingActionOperator
        H N hN beta hbeta left right

theorem periodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordPackage H N hN beta hbeta :=
  { physicalToAmbient := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_coe H N hN beta hbeta
    sliceInsertion := periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWordPhysicalOperator_eq H N hN beta hbeta
    slabInsertion := periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq H N hN beta hbeta
    spatialWilson := periodicHypercubicEvenSpecialUnitaryFiniteTransferSpatialWilsonWordPhysicalOperator_eq H N hN beta hbeta
    temporalCrossing := periodicHypercubicEvenSpecialUnitaryFiniteTransferTemporalCrossingWordPhysicalOperator_eq H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
