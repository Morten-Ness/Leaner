import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem single_v_eq_zero {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hp' : p' ≠ p) :
    (CochainComplex.HomComplex.Cochain.single f n).v p' q' hpq' = 0 := by
  dsimp [CochainComplex.HomComplex.Cochain.single]
  rw [dif_neg]
  intro h
  exact hp' (by lia)

