import Mathlib

open scoped symmDiff

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_symmDiff (s t : Set α) (f : α → M) :
    mulIndicator (s ∆ t) f = mulIndicator (s \ t) f * mulIndicator (t \ s) f := Set.mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

