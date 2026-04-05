import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem normalizer_eq_top_iff : normalizer (H : Set G) = ⊤ ↔ H.Normal := eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => inv_mul_cancel_left a b ▸ h.mem_comm_iff.mp hb⟩⟩

