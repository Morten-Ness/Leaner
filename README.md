# Leaner


lake env lean --json ... returns structured diagnostics with pos and endPos, which is enough to recover the exact underlined span. This simple fact is incredibly useful when training LLMs to solve math problems.

First batch:
1513 proofs: LLM successes: 811. LLM Failures: 713. Model: gpt5.4.

