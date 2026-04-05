import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

variable {n} {D : Type*} [Category* D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

theorem map_v (p q : ℤ) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

