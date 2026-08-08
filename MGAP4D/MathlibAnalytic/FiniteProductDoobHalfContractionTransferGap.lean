import MGAP4D.MathlibAnalytic.FiniteProductDoobCouplingVariation
import MGAP4D.MathlibAnalytic.FiniteDimensionalPositiveSpectralSupportHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteKernelGroundStateDoobData

variable {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]

/-- A direct parallel Doob variation certificate transports exactly to a
Perron-orthogonal Rayleigh estimate for the original normalized transfer. -/
theorem transfer_rayleigh_le_of_doobParallelVariation
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (x : FiniteBoundaryHilbert (ι → G))
    (hx : inner ℝ x D.ground = 0) :
    inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
      C.variationData.coefficient * ‖x‖ ^ 2 := by
  apply D.transfer_rayleigh_le_of_weightedDoob C.variationData.coefficient
  · intro f hMean
    exact finiteProductDoob_centered_parallel_rayleigh_le D C f hMean
  · exact hx

/-- If the direct Doob variation coefficient is at most one half, the original
normalized transfer has the same one-half Rayleigh bound on the Perron
orthogonal sector. -/
theorem transfer_rayleigh_le_half_of_doobParallelVariation
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (hHalf : C.variationData.coefficient ≤ (1 / 2 : ℝ))
    (x : FiniteBoundaryHilbert (ι → G))
    (hx : inner ℝ x D.ground = 0) :
    inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
      (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  exact le_trans
    (D.transfer_rayleigh_le_of_doobParallelVariation C x hx)
    (mul_le_mul_of_nonneg_right hHalf (sq_nonneg ‖x‖))

/-- Any nonzero Perron-orthogonal transfer eigenvector inherits the direct
Doob variation coefficient as an upper bound on its eigenvalue. -/
theorem transfer_eigenvalue_le_of_doobParallelVariation
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (x : FiniteBoundaryHilbert (ι → G))
    (hxne : x ≠ 0)
    (hx : inner ℝ x D.ground = 0)
    (r : ℝ)
    (heig : finiteKernelNormalizedOperator D.kernel x = r • x) :
    r ≤ C.variationData.coefficient := by
  have hRayleigh := D.transfer_rayleigh_le_of_doobParallelVariation C x hx
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq] at hRayleigh
  have hnormsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxne)
  nlinarith

/-- In particular, a half-contractive Doob certificate forces every nonzero
Perron-orthogonal transfer eigenvalue below one half. -/
theorem transfer_eigenvalue_le_half_of_doobParallelVariation
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (hHalf : C.variationData.coefficient ≤ (1 / 2 : ℝ))
    (x : FiniteBoundaryHilbert (ι → G))
    (hxne : x ≠ 0)
    (hx : inner ℝ x D.ground = 0)
    (r : ℝ)
    (heig : finiteKernelNormalizedOperator D.kernel x = r • x) :
    r ≤ (1 / 2 : ℝ) :=
  le_trans
    (D.transfer_eigenvalue_le_of_doobParallelVariation C x hxne hx r heig)
    hHalf

/-- The scalar logarithmic consequence needed by the support-Hamiltonian
spine: a positive transfer eigenvalue at most one half has energy at least
`log 2`. -/
theorem log_two_le_neg_log_of_pos_le_half
    (r : ℝ)
    (hrpos : 0 < r)
    (hrhalf : r ≤ (1 / 2 : ℝ)) :
    Real.log 2 ≤ -Real.log r := by
  have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hlog := Real.strictMonoOn_log.monotoneOn hrpos.le hhalfpos.le hrhalf
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlogHalf] at hlog
  linarith

/-- Combined transfer-to-energy statement: a half-contractive Doob certificate
and a positive Perron-orthogonal transfer eigenmode yield the quantitative
energy lower bound `log 2`. -/
theorem log_two_le_neg_log_transfer_eigenvalue_of_doobParallelVariation
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (hHalf : C.variationData.coefficient ≤ (1 / 2 : ℝ))
    (x : FiniteBoundaryHilbert (ι → G))
    (hxne : x ≠ 0)
    (hx : inner ℝ x D.ground = 0)
    (r : ℝ)
    (hrpos : 0 < r)
    (heig : finiteKernelNormalizedOperator D.kernel x = r • x) :
    Real.log 2 ≤ -Real.log r := by
  exact log_two_le_neg_log_of_pos_le_half r hrpos
    (D.transfer_eigenvalue_le_half_of_doobParallelVariation
      C hHalf x hxne hx r heig)

/-- Audit-visible generic receipt for the quantitative half-contraction route. -/
structure DoobHalfContractionTransferGapPackage
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D) where
  coefficient_le_half : C.variationData.coefficient ≤ (1 / 2 : ℝ)
  transferRayleighHalf :
    ∀ x : FiniteBoundaryHilbert (ι → G),
      inner ℝ x D.ground = 0 →
        inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
          (1 / 2 : ℝ) * ‖x‖ ^ 2
  positiveEigenEnergyLogTwo :
    ∀ (x : FiniteBoundaryHilbert (ι → G)) (r : ℝ),
      x ≠ 0 →
      inner ℝ x D.ground = 0 →
      0 < r →
      finiteKernelNormalizedOperator D.kernel x = r • x →
      Real.log 2 ≤ -Real.log r

/-- Construct the generic quantitative receipt from a half-contractive direct
Doob variation certificate. -/
noncomputable def doobHalfContractionTransferGapPackage
    (D : FiniteKernelGroundStateDoobData (ι → G))
    (C : FiniteProductDoobParallelVariationCertificate D)
    (hHalf : C.variationData.coefficient ≤ (1 / 2 : ℝ)) :
    DoobHalfContractionTransferGapPackage D C :=
  { coefficient_le_half := hHalf
    transferRayleighHalf := fun x hx =>
      D.transfer_rayleigh_le_half_of_doobParallelVariation C hHalf x hx
    positiveEigenEnergyLogTwo := fun x r hxne hx hrpos heig =>
      D.log_two_le_neg_log_transfer_eigenvalue_of_doobParallelVariation
        C hHalf x hxne hx r hrpos heig }

end FiniteKernelGroundStateDoobData

end

end MathlibAnalytic
end MGAP4D
