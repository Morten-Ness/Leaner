import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_list_sum [AddMonoidWithOne R] (s : List ℕ) : (↑s.sum : R) = (s.map (↑)).sum := map_list_sum (castAddMonoidHom R) _

