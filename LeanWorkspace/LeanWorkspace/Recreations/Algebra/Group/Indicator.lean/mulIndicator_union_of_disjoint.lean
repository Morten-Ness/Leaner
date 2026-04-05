import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a := funext fun _ => Set.mulIndicator_union_of_notMem_inter (fun ha => h.le_bot ha) _

