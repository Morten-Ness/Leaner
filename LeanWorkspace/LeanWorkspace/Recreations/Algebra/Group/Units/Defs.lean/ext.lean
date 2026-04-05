import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := Units.val_injective huv

