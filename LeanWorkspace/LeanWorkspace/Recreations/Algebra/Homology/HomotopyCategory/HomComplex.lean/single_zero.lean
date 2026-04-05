import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem single_zero (p q n : ℤ) :
    (CochainComplex.HomComplex.Cochain.single (p := p) (q := q) 0 n : CochainComplex.HomComplex.Cochain K L n) = 0 := by
  CochainComplex.HomComplex.Cochain.ext p' q' hpq'
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq
      simp
    · simp [CochainComplex.HomComplex.Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ hp]

