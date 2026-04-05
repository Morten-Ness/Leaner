import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem isUnit_singleton (a : α) : IsUnit ({a} : Set α) := (Group.isUnit a).set

