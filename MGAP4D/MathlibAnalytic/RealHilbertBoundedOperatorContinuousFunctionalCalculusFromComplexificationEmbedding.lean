import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformCommutationFromContinuousFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace ContinuousFunctionalCalculus

set_option maxHeartbeats 400000

/-- Abstract operator-algebra data supplied by a complexification of a real Hilbert space.

The complexification map is required to be an isometric real star-algebra embedding and to preserve
the real spectrum.  No preservation hypothesis for continuous-functional-calculus values is included:
that fact is generated below from closedness of the range and Mathlib's elemental-subalgebra theorem. -/
structure RealHilbertBoundedOperatorComplexificationCFCDescentData
    (H HC : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC] where
  complexify : (H →L[ℝ] H) →⋆ₐ[ℝ] (HC →L[ℂ] HC)
  isometry_complexify : Isometry complexify
  real_spectrum_eq :
    ∀ T : H →L[ℝ] H, spectrum ℝ (complexify T) = spectrum ℝ T

namespace RealHilbertBoundedOperatorComplexificationCFCDescentData

variable {H HC : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- The complexification star-algebra homomorphism is injective. -/
theorem complexify_injective
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC) :
    Function.Injective D.complexify :=
  D.isometry_complexify.injective

/-- The range of an isometric complexification of the complete real operator algebra is closed. -/
theorem isClosed_range_complexify
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC) :
    IsClosed (D.complexify.range : Set (HC →L[ℂ] HC)) :=
  D.isometry_complexify.isClosedEmbedding.isClosed_range

/-- Self-adjointness is preserved by complexification. -/
theorem complexify_isSelfAdjoint
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (D.complexify T) := by
  show star (D.complexify T) = D.complexify T
  rw [← map_star, hT.star_eq]

/-- Self-adjointness is reflected by the injective complexification map. -/
theorem isSelfAdjoint_of_complexify
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    {T : H →L[ℝ] H} (hT : IsSelfAdjoint (D.complexify T)) :
    IsSelfAdjoint T := by
  show star T = T
  apply D.complexify_injective
  rw [map_star, hT.star_eq]

/-- The real-spectrum equality induces the required equivalence between continuous-function
algebras.  Its direction is chosen so that it feeds source functions into the complex CFC. -/
noncomputable def spectrumContinuousMapEquiv
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) :
    C(spectrum ℝ T, ℝ) ≃⋆ₐ[ℝ] C(spectrum ℝ (D.complexify T), ℝ) :=
  Homeomorph.compStarAlgEquiv' ℝ ℝ
    (Homeomorph.setCongr (D.real_spectrum_eq T))

/-- Precomposition along the spectrum homeomorphism does not change the range of a function. -/
theorem range_spectrumContinuousMapEquiv
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (f : C(spectrum ℝ T, ℝ)) :
    Set.range (D.spectrumContinuousMapEquiv T f) = Set.range f := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨(Homeomorph.setCongr (D.real_spectrum_eq T)) x, rfl⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨(Homeomorph.setCongr (D.real_spectrum_eq T)).symm x, by simp
      [spectrumContinuousMapEquiv]⟩

/-- Apply the complex-Hilbert real self-adjoint CFC after transporting the spectrum. -/
noncomputable def complexCfcAux
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    C(spectrum ℝ T, ℝ) →⋆ₐ[ℝ] (HC →L[ℂ] HC) :=
  (cfcHom (D.complexify_isSelfAdjoint hT)).comp
    (D.spectrumContinuousMapEquiv T)

/-- The auxiliary complex CFC is continuous. -/
theorem continuous_complexCfcAux
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    Continuous (D.complexCfcAux T hT) := by
  simpa only [complexCfcAux, StarAlgHom.coe_comp] using
    (cfcHom_continuous (D.complexify_isSelfAdjoint hT)).comp
      (ContinuousMap.continuous_precomp
        (Homeomorph.setCongr (D.real_spectrum_eq T)))

/-- The auxiliary complex CFC is injective. -/
theorem complexCfcAux_injective
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    Function.Injective (D.complexCfcAux T hT) := by
  intro f g hfg
  apply (D.spectrumContinuousMapEquiv T).injective
  apply cfcHom_injective (D.complexify_isSelfAdjoint hT)
  exact hfg

/-- The complex CFC image lies in the closed range of complexification.

This is generated from `cfcHom_mem_elemental`: the CFC image lies in the closed star subalgebra
generated by the complexified operator, and that elemental algebra is contained in the closed range. -/
theorem complexCfcAux_mem_range
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (f : C(spectrum ℝ T, ℝ)) :
    D.complexCfcAux T hT f ∈ D.complexify.range := by
  apply (StarAlgebra.elemental.le_of_mem D.isClosed_range_complexify
    (show D.complexify T ∈ D.complexify.range from ⟨T, rfl⟩))
  exact cfcHom_mem_elemental (D.complexify_isSelfAdjoint hT)
    (D.spectrumContinuousMapEquiv T f)

/-- The complexification embedding, identified with its range. -/
noncomputable def complexifyRangeEquiv
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC) :
    (H →L[ℝ] H) ≃⋆ₐ[ℝ] D.complexify.range :=
  StarAlgEquiv.ofInjective D.complexify D.complexify_injective

/-- Descend the complex CFC through the range equivalence back to real bounded operators. -/
noncomputable def descendedCfcHom
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    C(spectrum ℝ T, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H) :=
  ((D.complexifyRangeEquiv.symm :
      D.complexify.range →⋆ₐ[ℝ] (H →L[ℝ] H))).comp
    ((D.complexCfcAux T hT).codRestrict D.complexify.range
      (D.complexCfcAux_mem_range T hT))

/-- Applying complexification after descent recovers the auxiliary complex CFC exactly. -/
theorem complexify_descendedCfcHom
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (f : C(spectrum ℝ T, ℝ)) :
    D.complexify (D.descendedCfcHom T hT f) = D.complexCfcAux T hT f := by
  change D.complexify
      (D.complexifyRangeEquiv.symm
        ⟨D.complexCfcAux T hT f, D.complexCfcAux_mem_range T hT f⟩) =
    D.complexCfcAux T hT f
  let y : D.complexify.range :=
    ⟨D.complexCfcAux T hT f, D.complexCfcAux_mem_range T hT f⟩
  exact congrArg Subtype.val (D.complexifyRangeEquiv.apply_symm_apply y)

/-- Continuity descends because complexification is an isometric embedding. -/
theorem continuous_descendedCfcHom
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    Continuous (D.descendedCfcHom T hT) := by
  rw [← D.isometry_complexify.comp_continuous_iff]
  simpa only [Function.comp_def, D.complexify_descendedCfcHom T hT] using
    D.continuous_complexCfcAux T hT

/-- Injectivity descends from injectivity of the auxiliary complex CFC. -/
theorem descendedCfcHom_injective
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    Function.Injective (D.descendedCfcHom T hT) := by
  intro f g hfg
  apply D.complexCfcAux_injective T hT
  rw [← D.complexify_descendedCfcHom T hT f,
    ← D.complexify_descendedCfcHom T hT g, hfg]

/-- The descended CFC sends the identity function to the original real operator. -/
theorem descendedCfcHom_id
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    D.descendedCfcHom T hT
        ((ContinuousMap.id ℝ).restrict (spectrum ℝ T)) = T := by
  apply D.complexify_injective
  rw [D.complexify_descendedCfcHom]
  simpa [complexCfcAux, spectrumContinuousMapEquiv] using
    cfcHom_id (D.complexify_isSelfAdjoint hT)

/-- Spectral mapping descends through the spectrum-preserving complexification. -/
theorem spectrum_descendedCfcHom
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (f : C(spectrum ℝ T, ℝ)) :
    spectrum ℝ (D.descendedCfcHom T hT f) = Set.range f := by
  calc
    spectrum ℝ (D.descendedCfcHom T hT f) =
        spectrum ℝ (D.complexify (D.descendedCfcHom T hT f)) :=
      (D.real_spectrum_eq (D.descendedCfcHom T hT f)).symm
    _ = spectrum ℝ (D.complexCfcAux T hT f) := by
      rw [D.complexify_descendedCfcHom]
    _ = Set.range (D.spectrumContinuousMapEquiv T f) :=
      cfcHom_map_spectrum (D.complexify_isSelfAdjoint hT)
        (D.spectrumContinuousMapEquiv T f)
    _ = Set.range f := D.range_spectrumContinuousMapEquiv T f

/-- The descended CFC preserves self-adjointness. -/
theorem isSelfAdjoint_descendedCfcHom
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC)
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (f : C(spectrum ℝ T, ℝ)) :
    IsSelfAdjoint (D.descendedCfcHom T hT f) := by
  apply D.isSelfAdjoint_of_complexify
  rw [D.complexify_descendedCfcHom]
  exact cfcHom_predicate (D.complexify_isSelfAdjoint hT)
    (D.spectrumContinuousMapEquiv T f)

/-- An isometric, real-spectrum-preserving complexification embedding generates the complete
real-Hilbert bounded self-adjoint continuous functional calculus. -/
@[reducible]
noncomputable def toContinuousFunctionalCalculus
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC) :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint where
  predicate_zero := by simp
  compactSpace_spectrum := inferInstance
  spectrum_nonempty T hT := by
    letI : Nontrivial (HC →L[ℂ] HC) := by
      obtain ⟨S, U, hSU⟩ := exists_pair_ne (H →L[ℝ] H)
      exact nontrivial_of_ne (D.complexify S) (D.complexify U)
        (fun h => hSU (D.complexify_injective h))
    rw [← D.real_spectrum_eq T]
    exact ContinuousFunctionalCalculus.spectrum_nonempty
      (D.complexify T) (D.complexify_isSelfAdjoint hT)
  exists_cfc_of_predicate T hT :=
    ⟨D.descendedCfcHom T hT,
      D.continuous_descendedCfcHom T hT,
      D.descendedCfcHom_injective T hT,
      D.descendedCfcHom_id T hT,
      D.spectrum_descendedCfcHom T hT,
      D.isSelfAdjoint_descendedCfcHom T hT⟩

/-- Package the descended CFC in the existing bounded-transform interface. -/
noncomputable def toRealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (D : RealHilbertBoundedOperatorComplexificationCFCDescentData H HC) :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H where
  continuousFunctionalCalculus := D.toContinuousFunctionalCalculus

end RealHilbertBoundedOperatorComplexificationCFCDescentData

end

end MathlibAnalytic
end MGAP4D