import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_snoc (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → M) i) = (∏ i : Fin n, f i) * x := by
  simp [Fin.prod_univ_castSucc]

