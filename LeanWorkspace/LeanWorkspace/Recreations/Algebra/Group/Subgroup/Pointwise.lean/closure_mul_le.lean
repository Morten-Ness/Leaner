import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_mul_le (S T : Set G) : closure (S * T) ≤ closure S ⊔ closure T := sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

