import Mathlib

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

