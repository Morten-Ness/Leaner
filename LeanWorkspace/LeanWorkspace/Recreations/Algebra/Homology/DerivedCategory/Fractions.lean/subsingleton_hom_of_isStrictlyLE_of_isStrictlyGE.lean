import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE (X Y : CochainComplex C ℤ)
    (a b : ℤ) (h : a < b) [X.IsStrictlyLE a] [Y.IsStrictlyGE b] :
    Subsingleton (Q.obj X ⟶ Q.obj Y) := by
  suffices ∀ (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := DerivedCategory.right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b i (by lia)).eq_of_tgt
  rw [this, Q.map_zero, comp_zero]

