import Mathlib

variable (G : Type u) (H : Type v) [Mul G] [Mul H]

theorem _root_.MulEquiv.uniqueProds_iff (f : G ≃* H) : UniqueProds G ↔ UniqueProds H := ⟨UniqueProds.of_injective_mulHom f.symm f.symm.injective, UniqueProds.of_injective_mulHom f f.injective⟩

