import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem comap_lieSpan_range_eq {ι : Type*} (f : ι → K) :
    (LieSubalgebra.lieSpan R L (Set.range ((↑) ∘ f))).comap K.incl = LieSubalgebra.lieSpan R K (Set.range f) := by
  apply le_antisymm
  · intro ⟨x, hx⟩ hx'
    simp only [mem_comap, LieSubalgebra.coe_incl] at hx'
    suffices x ∈ (LieSubalgebra.lieSpan R K (Set.range f)).map K.incl by aesop
    clear hx
    induction hx' using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      have (i : ι) : f i ∈ LieSubalgebra.lieSpan R K (Set.range f) := LieSubalgebra.subset_lieSpan <| LieHom.mem_range_self i
      aesop
    | zero => exact LieSubalgebra.zero_mem _
    | add u v _ _ hu hv => revert hu hv; exact LieSubalgebra.add_mem
    | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
    | lie u v _ _ hu hv => revert hu hv; exact LieSubalgebra.lie_mem _
  · rw [LieSubalgebra.lieSpan_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, LieSubalgebra.coe_incl]
    exact LieSubalgebra.subset_lieSpan <| by simp

