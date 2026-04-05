import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

theorem map_comp_map :
    h.map h' fK fL f_comm ≫ h'.map h'' fK' fL' f_comm'
     = h.map h'' (fK ≫ fK') (fL ≫ fL') (by simp [f_comm', reassoc_of% f_comm]) := by
  ext (m | _ | m) <;> simp; rfl

