import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem sum_ne_zero_of_injOn_supDegree (hs : s.Nonempty)
    (hf : ∀ i ∈ s, f i ≠ 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 := let ⟨i, hi⟩ := hs
  AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

