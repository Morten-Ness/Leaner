import Mathlib

open scoped Pointwise

variable {A : Type u} {B : Type v}

variable [Group A] [Group B]

theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

