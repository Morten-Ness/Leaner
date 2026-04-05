import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

theorem shape (n m : ℤ) (hnm : n + 1 ≠ m) : h.d n m = 0 := match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; lia)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using K.shape n m (by simp at hnm ⊢; lia)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ | n := n
    · obtain _ | m := m
      · simp at hnm
      · rfl
    · simp only [CochainComplex.ConnectData.d]

