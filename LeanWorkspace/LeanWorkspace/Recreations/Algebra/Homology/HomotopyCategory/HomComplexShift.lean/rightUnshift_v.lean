import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem rightUnshift_v {n' a : ℤ} (γ : CochainComplex.HomComplex.Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [CochainComplex.HomComplex.Cochain.rightUnshift]
  simp only [mk_v]

