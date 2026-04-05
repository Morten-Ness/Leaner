import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_one (s : Set α) : (Set.mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) := Set.mulIndicator_eq_one.2 <| by simp only [mulSupport_fun_one, empty_disjoint]

