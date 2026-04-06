FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s := by
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right] at hv
  rcases hv with ⟨p1, hp1, hEq⟩
  rw [hEq]
  simpa [vsub_vadd] using s.affineCombination_mem ℕ (fun q => q ∈ ({p1, p} : Set P))
    (fun q hq => by
      rcases hq with rfl | rfl
      · exact hp1
      · exact hp)
    (fun q => if q = p1 then (1 : ℕ) else if q = p then 1 else 0)
    (by
      simp [Finset.mem_insert, Finset.mem_singleton])
    (by
      simp [Finset.sum_ite_eq, Finset.mem_insert, Finset.mem_singleton, add_comm])
