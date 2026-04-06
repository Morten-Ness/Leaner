import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_pow_pos_of_zero_notMem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) := by
  classical
  rw [Finsupp.prod]
  refine Finset.prod_pos ?_
  intro a ha
  exact pow_pos (Nat.pos_of_ne_zero fun h => nhf <| by simpa [Finsupp.mem_support_iff, h] using ha) _
