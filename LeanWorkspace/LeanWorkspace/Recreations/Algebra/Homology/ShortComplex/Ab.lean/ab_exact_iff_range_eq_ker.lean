import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.hom.range = S.g.hom.ker := by
  rw [CategoryTheory.ShortComplex.ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker, ← ConcreteCategory.comp_apply, S.zero]
    rfl
  · intro h
    rw [h]

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

