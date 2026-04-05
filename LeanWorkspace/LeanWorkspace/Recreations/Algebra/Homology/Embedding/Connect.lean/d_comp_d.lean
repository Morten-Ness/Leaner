import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

set_option backward.isDefEq.respectTransparency false in
theorem d_comp_d (n m p : ℤ) : h.d n m ≫ h.d m p = 0 := by
  by_cases hnm : n + 1 = m; swap
  · rw [CochainComplex.ConnectData.shape h n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [CochainComplex.ConnectData.shape h m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; lia
    simp only [Int.ofNat_eq_natCast, X_ofNat, d_ofNat, HomologicalComplex.d_comp_d]
  · obtain rfl : m = 0 := by lia
    obtain rfl : p = 1 := by lia
    simp
  · obtain rfl : m = -1 := by lia
    obtain rfl : p = 0 := by lia
    simp
  · obtain rfl : m = .negSucc (n + 1) := by lia
    obtain rfl : p = .negSucc n := by lia
    simp

