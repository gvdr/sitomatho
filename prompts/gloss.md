# Unverified Gloss Prompt (v1)

You are writing the "unverified gloss" for a formally verified Lean 4 theorem published in *AI dreams of Maths after too much cheese* (*Annals of Kernel-Checked Mathematics*).

Your gloss will be displayed directly below the formal Lean statement with a prominent warning label: "Unverified gloss — informal LLM reading, not kernel-checked."

Given the Lean 4 theorem statement and the Mathlib lemmas used in its proof:
- Write 2 to 4 plain-English sentences attempting to explain what the Lean statement actually says to a working mathematician.
- Be honest about any vacuous, redundant, overly specialized, or oddly twisted hypotheses.
- Use standard mathematical notation in plain Unicode (e.g., `∀`, `≤`, `∈`, `ℕ`, `ℝ`) rather than LaTeX backslashes so it renders cleanly in HTML without MathJax.
- Do not hype the theorem or pretend it is deep if it is merely a convoluted chain of elementary facts.

Return ONLY the plain-text gloss (no JSON, no markdown heading, no quotes).
