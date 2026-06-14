import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile smoke for the physical Hilbert construction

`positive-time Euclidean observables → OS seminorm → separation quotient →
Hilbert completion`. -/
theorem euclidean_yang_mills_os_physical_hilbert_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    InnerProductSpace ℝ P.OSSeparatedPreHilbert ∧
      InnerProductSpace ℝ P.PhysicalHilbert ∧
      CompleteSpace P.PhysicalHilbert ∧
      DenseRange
        (fun x : P.OSSeparatedPreHilbert => (x : P.PhysicalHilbert)) := by
  exact ⟨os_separated_preHilbert_innerProductSpace P,
    os_physical_hilbert_innerProductSpace P,
    os_physical_hilbert_complete P,
    os_preHilbert_dense_in_physical P⟩

/-- Compile smoke forcing the reconstructed Hamiltonian/PVM model to use the OS
completion as its Hilbert carrier. -/
theorem euclidean_yang_mills_os_reconstructed_model_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.H = M.observables.PhysicalHilbert ∧
      CompleteSpace M.toExplicitModel.H ∧
      M.toExplicitModel.vacuum = M.observables.vacuum ∧
      IsSelfAdjoint M.toExplicitModel.hamiltonian := by
  exact ⟨os_physical_reconstructed_model_hilbert_identified M,
    os_physical_reconstructed_model_complete M,
    os_physical_reconstructed_model_vacuum_eq_os_class M,
    M.hamiltonianSelfAdjoint⟩

/-- The OS inner product remains visibly tied to the continuum Euclidean
Yang--Mills measure in the compile target. -/
theorem euclidean_yang_mills_os_inner_measure_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F G : P.PositiveTimeObservable) :
    inner ℝ F G =
      ∫ ω,
        P.realization F (P.timeReflection ω) * P.realization G ω
        ∂S.measurePackage.euclideanMeasure := by
  exact os_positive_time_inner_eq_euclidean_integral P F G

end

end MathlibAnalytic
end MGAP4D
