import Mathlib

variable (G : Type u) (H : Type v) [Mul G] [Mul H]

theorem _root_.MulEquiv.twoUniqueProds_iff (f : G ≃* H) : TwoUniqueProds G ↔ TwoUniqueProds H := ⟨TwoUniqueProds.of_injective_mulHom f.symm f.symm.injective, TwoUniqueProds.of_injective_mulHom f f.injective⟩

