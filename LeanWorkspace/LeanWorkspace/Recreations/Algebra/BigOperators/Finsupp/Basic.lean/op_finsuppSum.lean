import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable {ι M N : Type*} [AddCommMonoid M] [Zero N]

theorem op_finsuppSum (f : ι →₀ N) (g : ι → N → M) :
    op (f.sum g) = f.sum fun i n ↦ op (g i n) := op_sum ..

