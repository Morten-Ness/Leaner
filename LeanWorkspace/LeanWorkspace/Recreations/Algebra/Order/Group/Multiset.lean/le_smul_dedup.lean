import Mathlib

variable {α β : Type*}

theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s := ⟨(s.map fun a => count a s).fold max 0,
    le_iff_count.2 fun a => by
      rw [Multiset.count_nsmul]; by_cases h : a ∈ s
      · grw [← one_le_count_iff_mem.2 <| mem_dedup.2 h]
        have : count a s ≤ fold max 0 (map (fun a => count a s) (a ::ₘ erase s a)) := by
          simp
        rw [cons_erase h] at this
        simpa [mul_succ] using this
      · simp [count_eq_zero.2 h, Nat.zero_le]⟩

