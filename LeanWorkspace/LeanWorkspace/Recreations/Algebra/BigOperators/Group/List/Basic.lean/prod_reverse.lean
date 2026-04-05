import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_reverse [One α] [Mul α] [@Std.Associative α (· * ·)] [@Std.Commutative α (· * ·)]
    [@Std.LawfulLeftIdentity α α (· * ·) 1] (l : List α) : prod l.reverse = prod l := @List.sum_reverse α ⟨1⟩ ⟨(· * ·)⟩ _ _ _ l

