import Mathlib

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

theorem triangleOfSES_distinguished :
    DerivedCategory.triangleOfSES hS ∈ distTriang (DerivedCategory C) := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨DerivedCategory.triangleOfSESIso hS⟩⟩

end
