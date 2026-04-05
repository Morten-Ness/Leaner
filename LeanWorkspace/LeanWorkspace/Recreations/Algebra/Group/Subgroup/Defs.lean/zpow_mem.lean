import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

theorem zpow_mem {x : M} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K
  | (n : ℕ) => by
    rw [zpow_natCast]
    exact pow_mem hx n
  | -[n+1] => by
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx n.succ)
