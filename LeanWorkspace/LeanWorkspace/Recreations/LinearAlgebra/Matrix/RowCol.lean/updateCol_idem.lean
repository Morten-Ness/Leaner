import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_idem [DecidableEq n] (A : Matrix m n α) (j : n) (x y : m → α) :
    (A.updateCol j x).updateCol j y = A.updateCol j y := by
  simpa only [Matrix.updateRow_transpose] using congr_arg transpose <| Matrix.updateRow_idem Aᵀ j x y

