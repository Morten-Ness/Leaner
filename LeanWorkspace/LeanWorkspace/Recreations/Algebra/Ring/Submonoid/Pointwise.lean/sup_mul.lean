import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P := le_antisymm (AddSubmonoid.mul_le.mpr fun mn hmn p hp ↦ by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
    rw [right_distrib]; exact add_mem_sup (AddSubmonoid.mul_mem_mul hm hp) <| AddSubmonoid.mul_mem_mul hn hp)
    (sup_le (AddSubmonoid.mul_le_mul_left le_sup_left) <| AddSubmonoid.mul_le_mul_left le_sup_right)

