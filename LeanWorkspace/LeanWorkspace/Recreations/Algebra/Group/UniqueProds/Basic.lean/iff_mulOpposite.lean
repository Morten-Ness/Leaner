import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem iff_mulOpposite :
    UniqueMul (B.map ⟨_, op_injective⟩) (A.map ⟨_, op_injective⟩) (op b0) (op a0) ↔
      UniqueMul A B a0 b0 := ⟨UniqueMul.of_mulOpposite, UniqueMul.to_mulOpposite⟩

