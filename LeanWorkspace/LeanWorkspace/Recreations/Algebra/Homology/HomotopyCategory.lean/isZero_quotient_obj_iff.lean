import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem isZero_quotient_obj_iff (C : HomologicalComplex V c) :
    IsZero ((HomotopyCategory.quotient _ _).obj C) ↔ Nonempty (Homotopy (𝟙 C) 0) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(HomotopyCategory.homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (HomotopyCategory.eq_of_homotopy _ _ h)

