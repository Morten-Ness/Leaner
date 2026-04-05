import Mathlib

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

