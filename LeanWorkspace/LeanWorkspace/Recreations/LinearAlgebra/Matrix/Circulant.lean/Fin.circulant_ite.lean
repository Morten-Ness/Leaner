import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_ite (α) [Zero α] [One α] :
    ∀ n, Matrix.circulant (fun i => ite (i.1 = 0) 1 0 : Fin n → α) = 1
  | 0 => by simp [eq_iff_true_of_subsingleton]
  | n + 1 => by
    rw [← Matrix.circulant_single_one]
    congr with j
    simp [Pi.single_apply]
