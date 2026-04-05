import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (γ' : CochainComplex.HomComplex.Cochain L M m)
    (h : n + m = t) (ht' : t + a = t') :
    (γ.comp γ' h).leftShift a t' ht' = (a * m).negOnePow • (γ.leftShift a n' hn').comp γ'
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext p q hpq
  have h' : n' + m = t' := by lia
  dsimp
  simp only [CochainComplex.HomComplex.Cochain.comp_v _ _ h' p (p + n') q rfl (by lia),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
    CochainComplex.HomComplex.Cochain.leftShift_v (γ.comp γ' h) a t' (by lia) p q hpq (p + a) (by lia),
    smul_smul, Linear.units_smul_comp, assoc, Int.negOnePow_add, ← mul_assoc, ← h',
    comp_v _ _ h (p + a) (p + n') q (by lia) (by lia)]
  congr 2
  rw [add_comm n', mul_add, Int.negOnePow_add]

