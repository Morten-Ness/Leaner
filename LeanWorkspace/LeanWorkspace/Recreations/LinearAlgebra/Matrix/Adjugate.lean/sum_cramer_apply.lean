import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x ∈ s, Matrix.cramer A (fun j => f j x) i) = Matrix.cramer A (fun j : n => ∑ x ∈ s, f j x) i := calc
    (∑ x ∈ s, Matrix.cramer A (fun j => f j x) i) = (∑ x ∈ s, Matrix.cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = Matrix.cramer A (fun j : n => ∑ x ∈ s, f j x) i := by
      rw [Matrix.sum_cramer, Matrix.cramer_apply]
      congr with j
      apply Finset.sum_apply

