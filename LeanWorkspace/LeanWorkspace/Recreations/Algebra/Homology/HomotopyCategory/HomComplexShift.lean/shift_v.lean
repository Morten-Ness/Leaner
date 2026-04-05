import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

