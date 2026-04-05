import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p p'
        (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p + a := by lia
  dsimp only [CochainComplex.HomComplex.Cochain.leftShift]
  simp only [mk_v]

