# Leaner

This repo is for building Lean finetuning data from mathlib.

The big picture is:

* create high-quality Lean theorem/proof examples from mathlib
* compare verified human/mathlib proofs against LLM-generated proofs
* use that as data and infrastructure for finetuning or benchmarking Lean theorem-proving models.

lake env lean --json ... returns structured diagnostics with pos and endPos, which is enough to recover the exact underlined span. This simple fact is incredibly useful when training LLMs to solve math problems.

First batch:
1513 proofs: LLM successes: 811. LLM Failures: 713. Model: gpt5.4.

