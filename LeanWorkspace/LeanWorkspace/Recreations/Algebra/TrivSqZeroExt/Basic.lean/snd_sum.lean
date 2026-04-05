import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd := Prod.snd_sum

