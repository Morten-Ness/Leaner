import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem d_comp_ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (CochainComplex.HomComplex.Cochain.ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q := by
  rw [add_zero] at hpq
  subst hpq
  rw [CochainComplex.HomComplex.Cochain.ofHoms_v]

