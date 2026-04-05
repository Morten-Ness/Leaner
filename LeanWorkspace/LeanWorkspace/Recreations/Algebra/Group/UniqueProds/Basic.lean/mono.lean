import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mono {A' B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (h : UniqueMul A' B' a0 b0) :
    UniqueMul A B a0 b0 := fun _ _ ha hb he ↦ h (hA ha) (hB hb) he

