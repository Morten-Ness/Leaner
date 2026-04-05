import Mathlib

variable {R : Type u} {α : Type*}

theorem add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a := calc
    a + 1 ≤ a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

