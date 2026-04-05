import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

theorem lieIdeal_oper_eq_linear_span [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } := by
  apply le_antisymm
  · let s := { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
    have aux : ∀ (y : L), ∀ m' ∈ Submodule.span R s, ⁅y, m'⁆ ∈ Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ ↦ ⁅y, m'⁆ ∈ Submodule.span R s) ?_ ?_ ?_ ?_ hm'
      · rintro m'' ⟨x, n, hm''⟩; rw [← hm'', leibniz_lie]
        refine Submodule.add_mem _ ?_ ?_ <;> apply Submodule.subset_span
        · use ⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n
        · use x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩
      · simp
      · intro m₁ m₂ _ _ hm₁ hm₂; rw [lie_add]; exact Submodule.add_mem _ hm₁ hm₂
      · intro t m'' _ hm''; rw [lie_smul]; exact Submodule.smul_mem _ t hm''
    change _ ≤ ({ Submodule.span R s with lie_mem := fun hm' => aux _ _ hm' } : LieSubmodule R L M)
    rw [LieSubmodule.lieIdeal_oper_eq_span, lieSpan_le]
    exact Submodule.subset_span
  · rw [LieSubmodule.lieIdeal_oper_eq_span]; apply submodule_span_le_lieSpan

