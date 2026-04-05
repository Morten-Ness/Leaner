import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem left_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

