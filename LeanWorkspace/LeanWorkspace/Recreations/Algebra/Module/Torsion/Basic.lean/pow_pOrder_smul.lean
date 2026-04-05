import Mathlib

variable {R M : Type*}

variable [Monoid R] [AddCommMonoid M] [DistribMulAction R M]

theorem pow_pOrder_smul {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M)
    [∀ n : ℕ, Decidable (p ^ n • x = 0)] : p ^ Submodule.pOrder hM x • x = 0 := Nat.find_spec <| (Submodule.isTorsion'_powers_iff p).mp hM x

