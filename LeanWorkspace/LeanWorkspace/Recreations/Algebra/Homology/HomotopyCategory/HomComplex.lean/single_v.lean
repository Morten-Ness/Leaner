import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem single_v {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (hpq : p + n = q) :
    (CochainComplex.HomComplex.Cochain.single f n).v p q hpq = f := by
  dsimp [CochainComplex.HomComplex.Cochain.single]
  rw [if_pos, id_comp, comp_id]
  tauto

