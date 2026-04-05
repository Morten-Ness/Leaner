import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHoms_zero : CochainComplex.HomComplex.Cochain.ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0 := by cat_disch

