import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

variable [IsTrans N r] (m : M) {a b c : N}

theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c := _root_.trans (act_rel_act_of_rel m ab) rl

