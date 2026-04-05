import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

include hij in
theorem composableArrows₃_exact [CategoryWithHomology C] :
    (HomologicalComplex.HomologySequence.composableArrows₃ K i j).Exact := by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

