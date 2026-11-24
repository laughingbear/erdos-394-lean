# Erdős Problem 394 — lower bound, formalized in Lean 4

Proof of `Erdos394.erdos_394.variants.lower_bound` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/394.lean`):

$$\sum_{n\le x} t_2(n) \gg \frac{x^2}{\log x},$$

where $t_2(n)$ is the least $m \ge 1$ with $n \mid m(m+1)$.

* Depends only on Mathlib (pinned to the same revision as formal-conjectures; Lean v4.33.1).
* `#print axioms Erdos394.erdos_394.variants.lower_bound` → `[propext, Classical.choice, Quot.sound]`.
* The definition `t`, the lemma `t_eq_of` and the `≪` notation are copied verbatim from formal-conjectures.

Build: `lake exe cache get && lake build`.

Prepared with AI assistance (Claude); the statement match and axioms were checked by compiling.
