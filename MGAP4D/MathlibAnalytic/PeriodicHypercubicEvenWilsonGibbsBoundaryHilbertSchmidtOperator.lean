import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryGramHilbertSchmidt
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
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

/-- The actual compact Wilson shared-boundary Gram kernel, viewed through the
generic Fréchet--Riesz Hilbert--Schmidt construction as a bounded operator on
boundary Haar `L²`.

The carrier is written explicitly here.  The same type is already named
`PeriodicHypercubicEvenSpecialUnitaryBoundaryL2` in the physical Yang--Mills
OS spine, so no duplicate alias is introduced in this lower analytic layer. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  realL2HilbertSchmidtKernelOperator
    (μ := periodicHypercubicEvenBoundaryHaarMeasure H N)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta)

/-- Exact matrix coefficient of the actual compact Wilson boundary
Hilbert--Schmidt operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
          H N hN beta hbeta) f g := by
  exact realL2HilbertSchmidtKernelOperator_inner
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta) f g

/-- The actual boundary operator norm is bounded by the Hilbert--Schmidt norm
of the physical shared-boundary Gram kernel. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta‖ := by
  exact realL2HilbertSchmidtKernelOperator_norm_le
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta)

/-- Squared operator norm is bounded by the exact boundary-pair Haar integral
of the squared physical Gram kernel. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_sq_le_integral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ ^ 2 ≤
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryPairHaarMeasure H N) := by
  have hnorm :=
    periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le
      H N hN beta hbeta
  have h0 :
      0 ≤ ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ := norm_nonneg _
  have hk0 :
      0 ≤ ‖periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta‖ := norm_nonneg _
  rw [← periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_norm_sq
    H N hN beta hbeta]
  nlinarith

/-- The operator norm has a direct finite-volume partition-function bound.
The boundary Haar measure is normalized probability measure, so the
Hilbert--Schmidt norm of a kernel uniformly bounded by `Z⁻¹` is at most
`Z⁻¹`. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le_inv_partitionFunction
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ ≤
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction⁻¹ := by
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
    H N hN beta hbeta
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let zinv : ℝ := C.base.partitionFunction⁻¹
  have hop :
      ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
          H N hN beta hbeta‖ ≤ ‖K‖ := by
    simpa [K] using
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le
        H N hN beta hbeta
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hzinv : 0 ≤ zinv := le_of_lt (inv_pos.mpr hZ)
  have hkSq : ‖K‖ ^ 2 ≤ zinv ^ 2 := by
    rw [periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_norm_sq]
    let pairMeasure := periodicHypercubicEvenBoundaryPairHaarMeasure H N
    letI : IsProbabilityMeasure pairMeasure := by
      dsimp [pairMeasure, periodicHypercubicEvenBoundaryPairHaarMeasure,
        periodicHypercubicEvenBoundaryHaarMeasure,
        FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
      infer_instance
    have hpoint : ∀ p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2 ≤ zinv ^ 2 := by
      intro p
      have h :=
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_abs_le_inv_partitionFunction
          H N hN beta hbeta p.1 p.2
      have hnonneg : 0 ≤
          |periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
            H N hN beta hbeta p.1 p.2| := abs_nonneg _
      have hsquare :
          |periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
            H N hN beta hbeta p.1 p.2| ^ 2 ≤ zinv ^ 2 := by
        nlinarith
      simpa [Real.norm_eq_abs] using hsquare
    calc
      (∫ p,
          ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
            H N hN beta hbeta p.1 p.2‖ ^ 2 ∂pairMeasure) ≤
          ∫ _p, zinv ^ 2 ∂pairMeasure := by
        exact integral_mono_ae
          (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_norm_sq_integrable
            H N hN beta hbeta)
          (integrable_const (zinv ^ 2))
          (Filter.Eventually.of_forall hpoint)
      _ = zinv ^ 2 := by simp
  have hk : ‖K‖ ≤ zinv := by
    nlinarith [norm_nonneg K]
  exact hop.trans (by simpa [K, zinv, C] using hk)

/-- Audit-visible actual compact-Wilson Hilbert--Schmidt boundary-operator
receipt.  Positivity and symmetry are deliberately separated into the next
Gram-factorization package rather than assumed here. -/
structure PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperatorPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  innerFormula :
    ∀ f g : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N),
      inner ℝ
          (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
            H N hN beta hbeta f) g =
        realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
            H N hN beta hbeta) f g
  normLeKernel :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta‖
  normLeInvPartitionFunction :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ ≤
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction⁻¹

/-- Construct the actual compact-Wilson Hilbert--Schmidt boundary operator
receipt. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperatorPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperatorPackage
      H N hN beta hbeta :=
  { innerFormula :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_inner
        H N hN beta hbeta
    normLeKernel :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le
        H N hN beta hbeta
    normLeInvPartitionFunction :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_le_inv_partitionFunction
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
