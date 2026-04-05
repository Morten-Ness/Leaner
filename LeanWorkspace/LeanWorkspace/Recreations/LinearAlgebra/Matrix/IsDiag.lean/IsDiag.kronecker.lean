import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.kronecker [MulZeroClass α] {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsDiag)
    (hB : B.IsDiag) : (A ⊗ₖ B).IsDiag := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk_inj, Ne, not_and_or] at h
  rcases h with hac | hbd
  · simp [hA hac]
  · simp [hB hbd]

