import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [ContravariantClass M N μ r]

variable [IsTrans N r] (m : M) {a b c : N}

theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c := _root_.trans ab (rel_of_act_rel_act m rl)

