import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [i : CovariantClass N N mu r]
  [i' : CovariantClass N N (swap mu) r] {a b c d : N}

theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) := _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

