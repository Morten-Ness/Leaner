import Mathlib

variable {R : Type u} [CommSemiring R]

theorem whiskerRight_apply {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n := rfl

