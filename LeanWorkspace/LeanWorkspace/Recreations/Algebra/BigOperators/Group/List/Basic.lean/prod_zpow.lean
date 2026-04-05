import Mathlib

variable {ι α β M N P G : Type*}

theorem prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod := let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

