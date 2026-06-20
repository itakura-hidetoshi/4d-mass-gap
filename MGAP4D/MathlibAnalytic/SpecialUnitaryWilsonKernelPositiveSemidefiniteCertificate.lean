import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefinite

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- A symmetric positive-semidefinite real kernel, the exact input required by
the Moore--Aronszajn/GNS construction. -/
structure RealKernelPositiveSemidefiniteCertificate
    (X : Type)
    (kernel : X → X → ℝ) : Prop where
  symmetric : ∀ x y, kernel x y = kernel y x
  positiveSemidefinite : RealKernelPositiveSemidefinite X kernel

/-- Every real Hilbert feature realization supplies the corresponding symmetric
positive-semidefinite kernel certificate. -/
theorem RealHilbertKernelFeature.toPositiveSemidefiniteCertificate
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel) :
    RealKernelPositiveSemidefiniteCertificate X kernel where
  symmetric := C.symmetric
  positiveSemidefinite := C.positiveSemidefinite

/-- For positive matrix size and nonnegative coupling, the exact Wilson
relative kernel is symmetric.  Symmetry is inherited from every finite Taylor
Hilbert feature and passed to the exact kernel by uniqueness of limits. -/
theorem specialUnitaryWilsonRelativeKernel_symmetric
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h =
      specialUnitaryWilsonRelativeKernel N beta h g := by
  have hApproxSymm :
      (fun degree =>
        specialUnitaryWilsonRelativeKernelPartial N beta degree g h) =ᶠ[atTop]
      (fun degree =>
        specialUnitaryWilsonRelativeKernelPartial N beta degree h g) := by
    exact Filter.Eventually.of_forall fun degree =>
      (specialUnitaryWilsonRelativeKernelPartialConcreteFeature
        N hN beta hbeta degree).symmetric g h
  have hForward :=
    specialUnitaryWilsonRelativeKernelPartial_tendsto N beta g h
  have hReverse :=
    specialUnitaryWilsonRelativeKernelPartial_tendsto N beta h g
  exact tendsto_nhds_unique hForward (hReverse.congr' hApproxSymm.symm)

/-- The exact one-plaquette Wilson relative kernel carries the complete
symmetric positive-semidefinite certificate needed for its generic GNS Hilbert
feature construction. -/
theorem specialUnitaryWilsonRelativeKernel_positiveSemidefiniteCertificate
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefiniteCertificate
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernel N beta) where
  symmetric := specialUnitaryWilsonRelativeKernel_symmetric N hN beta hbeta
  positiveSemidefinite :=
    specialUnitaryWilsonRelativeKernel_positiveSemidefinite N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
