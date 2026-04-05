import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.submatrix [Zero α] {A : Matrix n n α} (ha : A.IsDiag) {f : m → n}
    (hf : Function.Injective f) : (A.submatrix f f).IsDiag := fun _ _ h => ha (hf.ne h)

