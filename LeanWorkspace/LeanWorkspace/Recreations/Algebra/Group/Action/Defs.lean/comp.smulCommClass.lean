import Mathlib

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

