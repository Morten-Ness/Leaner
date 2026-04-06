FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_vadd (s : Finset ι) (w : ι → k) (p : ι → P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  classical
  simp only [Finset.weightedVSubOfPoint]
  apply Finset.sum_congr rfl
  intro c hc
  rw [vadd_vsub_assoc]
  have h : p c -ᵥ (-v +ᵥ b) = v + (p c -ᵥ b) := by
    rw [← vadd_vsub_assoc]
  rw [h, smul_add]
  abel
