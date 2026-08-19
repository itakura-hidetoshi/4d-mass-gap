import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap12
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap23
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumAxis1Reflection
import Mathlib.Tactic

/-!
# Finite signed-spatial generator words preserve the all-spatial zero-momentum observable

The concrete equal-weight all-spatial zero-momentum Wilson observable is already theorem-generated
invariant under the two adjacent spatial-axis swaps and under reflection of spatial axis `1`.
This file closes those three generator receipts under arbitrary finite composition.

The three constructors are deliberately presented as generators rather than prematurely identified
with an abstract cubic group.  A finite list acts recursively on the actual positive-link
configuration, and invariance of the observable follows by induction on the list.

Thus downstream work may reason with arbitrary words in `swap12`, `swap23`, and `reflect1` without
re-proving scalar invariance at every composition step.  Identification of the quotient of these
words with the finite signed-permutation group, a cubic irreducible-representation label, continuum
spin, and spectral mass claims remain separate downstream obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The three concrete spatial generators presently realized on the finite positive-link carrier. -/
inductive PeriodicHypercubicEvenSpatialSignedGenerator where
  | swap12
  | swap23
  | reflect1
  deriving DecidableEq, Fintype

/-- Action of one concrete signed-spatial generator on an actual finite `SU(N)` configuration. -/
def periodicHypercubicEvenSpatialSignedGeneratorAction
    {H N : ℕ}
    (g : PeriodicHypercubicEvenSpatialSignedGenerator)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  match g with
  | .swap12 => periodicHypercubicConfigurationSpatialAxisSwap12 A
  | .swap23 => periodicHypercubicConfigurationSpatialAxisSwap23 A
  | .reflect1 => periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorAction_swap12
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorAction
        .swap12 A =
      periodicHypercubicConfigurationSpatialAxisSwap12 A :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorAction_swap23
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorAction
        .swap23 A =
      periodicHypercubicConfigurationSpatialAxisSwap23 A :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorAction_reflect1
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorAction
        .reflect1 A =
      periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A :=
  rfl

/-- Apply a finite generator word.  The head generator acts after the tail word, so list
concatenation corresponds to ordinary composition in the expected left-to-right theorem proofs. -/
def periodicHypercubicEvenSpatialSignedGeneratorWordAction
    {H N : ℕ} :
    List PeriodicHypercubicEvenSpatialSignedGenerator →
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ
  | [], A => A
  | g :: word, A =>
      periodicHypercubicEvenSpatialSignedGeneratorAction g
        (periodicHypercubicEvenSpatialSignedGeneratorWordAction word A)

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorWordAction_nil
    {H N : ℕ}
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorWordAction [] A = A :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialSignedGeneratorWordAction_cons
    {H N : ℕ}
    (g : PeriodicHypercubicEvenSpatialSignedGenerator)
    (word : List PeriodicHypercubicEvenSpatialSignedGenerator)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSignedGeneratorWordAction (g :: word) A =
      periodicHypercubicEvenSpatialSignedGeneratorAction g
        (periodicHypercubicEvenSpatialSignedGeneratorWordAction word A) :=
  rfl

/-- Each of the three concrete signed-spatial generators fixes the scalar all-spatial
zero-momentum normalized-real-trace observable. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_signedGeneratorInvariant
    (H N : ℕ)
    (g : PeriodicHypercubicEvenSpatialSignedGenerator)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenSpatialSignedGeneratorAction g A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  cases g with
  | swap12 =>
      exact
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap12Invariant
          H N A
  | swap23 =>
      exact
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap23Invariant
          H N A
  | reflect1 =>
      exact
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_axis1ReflectionInvariant
          H N A

/-- The observable is invariant under every finite word in the two adjacent swaps and the
independent axis-`1` reflection.  This is the composition closure needed before identifying the
resulting action with an abstract finite signed-permutation group. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_signedGeneratorWordInvariant
    (H N : ℕ)
    (word : List PeriodicHypercubicEvenSpatialSignedGenerator)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenSpatialSignedGeneratorWordAction word A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  induction word with
  | nil => rfl
  | cons g word ih =>
      calc
        periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
            (periodicHypercubicEvenSpatialSignedGeneratorWordAction (g :: word) A) =
          periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
            (periodicHypercubicEvenSpatialSignedGeneratorWordAction word A) := by
              exact
                periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_signedGeneratorInvariant
                  H N g
                  (periodicHypercubicEvenSpatialSignedGeneratorWordAction word A)
        _ = periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := ih

end

end MathlibAnalytic
end MGAP4D
