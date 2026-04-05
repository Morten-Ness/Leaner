import Mathlib

variable {M N : Type*}

theorem sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

