import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

theorem upper_two_blockTriangular [Zero R] [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) {a b : α} (hab : a < b) :
    Matrix.BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b) := by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_gt] at hcd ⊢

