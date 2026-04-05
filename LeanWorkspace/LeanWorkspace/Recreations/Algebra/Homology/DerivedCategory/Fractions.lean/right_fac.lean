import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem right_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

