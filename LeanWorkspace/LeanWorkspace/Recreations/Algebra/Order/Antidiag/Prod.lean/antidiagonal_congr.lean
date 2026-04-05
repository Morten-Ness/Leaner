import Mathlib

variable {A : Type*}

variable [AddCancelMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}

theorem antidiagonal_congr (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((add_right_inj q.fst).mp ?_)⟩
  rw [mem_antidiagonal] at hp hq
  rw [hq, ← h, hp]

