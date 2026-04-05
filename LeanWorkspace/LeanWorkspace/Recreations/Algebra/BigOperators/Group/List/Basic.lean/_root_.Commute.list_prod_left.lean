import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) :
    Commute l.prod y := ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm

