import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtOperator
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSymmetricKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

/-- The canonical `L²(boundary × boundary)` Wilson Gram kernel is represented
a.e. by the already-constructed physical scalar Gram kernel. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta p) =ᵐ[periodicHypercubicEvenBoundaryPairHaarMeasure H N]
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta p.1 p.2) := by
  exact
    (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_memLp_two
      H N hN beta hbeta).coeFn_toLp

/-- The actual compact Wilson scalar Gram representative is symmetric under
boundary-coordinate swap. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_rep_symmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealL2KernelRepresentativeSymmetric
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2) := by
  intro p
  exact periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_symmetric
    H N hN beta hbeta p.2 p.1

/-- The actual compact Wilson shared-boundary Hilbert--Schmidt kernel pairing
is symmetric on the complete boundary Haar `L²` space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingSymmetric
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta) := by
  exact realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta)
    (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
      H N hN beta hbeta p.1 p.2)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_coeFn
      H N hN beta hbeta)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_rep_symmetric
      H N hN beta hbeta)

/-- Therefore the actual compact Wilson shared-boundary Hilbert--Schmidt
operator is symmetric in Mathlib's real-Hilbert-space sense. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_isSymmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsSymmetric := by
  exact realL2HilbertSchmidtKernelOperator_isSymmetric
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta)
    (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
      H N hN beta hbeta)

/-- Audit-visible actual Wilson symmetry receipt. -/
structure PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtSymmetricPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  pairingSymmetric :
    RealL2HilbertSchmidtKernelPairingSymmetric
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
  operatorSymmetric :
    ((periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsSymmetric

/-- Construct the actual Wilson symmetry package. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtSymmetricPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtSymmetricPackage
      H N hN beta hbeta :=
  { pairingSymmetric :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
        H N hN beta hbeta
    operatorSymmetric :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_isSymmetric
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
