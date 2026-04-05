import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [ContravariantClass M N μ r]

variable [IsTrans N r] (m : M) {a b c : N}

theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) := _root_.trans (rel_of_act_rel_act m ab) rr

