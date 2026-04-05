import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

variable [IsTrans N r] (m : M) {a b c : N}

theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) := _root_.trans rr (act_rel_act_of_rel _ ab)

