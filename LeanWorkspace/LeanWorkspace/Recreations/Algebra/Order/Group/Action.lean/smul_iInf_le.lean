import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i := le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

