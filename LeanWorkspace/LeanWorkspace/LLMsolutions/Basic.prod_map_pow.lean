import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | @cons a m ih =>
      simp [ih, mul_pow]
