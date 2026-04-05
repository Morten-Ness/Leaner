import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_prod_map (m : Multiset ι) (n : Multiset κ) {f : ι → κ → M} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) := Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

