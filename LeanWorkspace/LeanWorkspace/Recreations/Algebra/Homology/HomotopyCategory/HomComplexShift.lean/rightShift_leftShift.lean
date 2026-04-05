import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem rightShift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').rightShift a n hn' =
      (a * n' + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [CochainComplex.HomComplex.Cochain.rightShift_v _ a n hn' p q hpq (q + a) (by lia),
    CochainComplex.HomComplex.Cochain.leftShift_v _ a n' hn' p (q + a) (by lia) (p + a) (by lia), units_smul_v, CochainComplex.HomComplex.Cochain.shift_v']
  dsimp
  rw [id_comp, comp_id]

