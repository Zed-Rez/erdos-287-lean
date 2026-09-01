# Kernel-checked results for Erdős Problem #287

Lean 4 / Mathlib formalizations around [Erdős problem #287](https://www.erdosproblems.com/287)
(Erdős–Graham): *if `1 = 1/n₁ + ⋯ + 1/n_k` with `1 < n₁ < ⋯ < n_k`, must some
consecutive gap `n_{i+1} − n_i` be at least 3?* The representation `{2, 3, 6}`
shows the constant 3 is best possible. The problem is open.

## Provenance — read this first

**These proofs are AI-generated and have not been aggressively human-reviewed.**
They were produced in August 2026 by an autonomous Claude (Opus 5) loop with human
prompting and orchestration by Reza Ramji, then independently rebuilt from source
against a second Mathlib checkout on a second machine. The trust model is the Lean
kernel, not human review:

- every theorem below type-checks with axioms exactly
  `[propext, Classical.choice, Quot.sound]`;
- the tree contains no `sorry`, no `admit`, no `native_decide`, no extra axioms
  (CI enforces this — see `scripts/audit.sh`);
- what deserves human scrutiny is the **statements**, which are short and are
  reproduced below. If a statement says what it appears to say, the kernel
  guarantees the rest.

Prose comments inside the files are the generating model's own lab notes; treat
them as commentary, not as verified claims.

## Headline results (all kernel-checked)

| theorem | statement |
|---|---|
| `Main2.erdos287_below` | **#287 holds for every representation whose largest denominator is ≤ 858,988,211,239,796,718,174,213 ≈ 8.59×10²³** (previous best kernel-checked range we are aware of: 4×10⁹) |
| `Kurschak.gap_at_least_two` | every representation (with `n₁ ≥ 2`) has some gap ≥ 2 — the `variants.gap_at_least_two` statement of [formal-conjectures 287.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/287.lean), previously `sorry` |
| `PCI.prime_conjecture_implies` | the prime-pair hypothesis on the problem page (for all large `N` a prime `P ∈ [N, 2N]` with `(P+1)/2` prime) implies #287 — the `variants.prime_conjecture_implies` statement, previously `sorry` |
| `Window4.window4` | all gaps ≤ 2 ⟹ `100·(M + 2) ≤ 739·n₁`, i.e. `M ≤ 7.39·n₁ − 2` (constant `e²` is sharp for the method) |
| `Lower3.lower3` | `2718·n₁ ≤ 1000·M + 2718`, i.e. `n₁ ≤ M/e + 1` — **no gap hypothesis**, true of every Egyptian representation of 1 |
| `KFinal.kbound` | all gaps ≤ 2 ⟹ `6389·M ≤ 14778·(k+1)`; the constant `2/(1−e⁻²)` is optimal for the archimedean data |
| `Bertrand134.g1_ge_134` | all gaps ≤ 2 and `M ≥ 10¹⁸⁹` ⟹ at least 134 of the gaps equal 1 (via Bertrand: an explicit large prime none of whose window multiples can be a denominator) |
| `G3Ext.g3_all_ext` | `{2, 3, 6}` is the **only** representation with all gaps ≤ 3 and `M ≤ 2.62×10³⁵` |
| `Egyptian.largest_not_prime`, `…_not_prime_power`, `…cofactor_bound` | in any Egyptian representation of 1, the largest denominator `M` is never a prime or prime power, and `M = a·p` (`p` prime) forces `p ≤ a·a!` — so `M/P(M) ≳ log M / log log M` |
| `QLaw.qlaw`, `Cascade.cascade` | q-adic counting laws: at every prime `q`, `∑_{v_q(n)=e} (n/q^e)⁻¹ = 0` in `ZMod q`, plus a 2-adic cascade one level deeper |
| `Budget.budget` | the reciprocal mass of any provable set of non-denominators is at most `H(n₁, M) − 1` — a closure criterion needing no consecutive pair |
| `IndepRank` / `IndepDual` / `AltChain` / `ParitySwitch` / `RoughChain` / `GapOne` | the parity machinery: greedy sets extremize reciprocal sums of gap-independent sets in both directions, parity alternations force gap-1 steps, and a single free odd prime yields an alternating chain |

## Verify it yourself

```
lake exe cache get
lake build
bash scripts/audit.sh
```

The audit recompiles `Check.lean` and asserts that all 23 audited theorems
report exactly `[propext, Classical.choice, Quot.sound]`. Note the build sets
`--tstack=200000` (in `lakefile.toml`): the `LadderG3S*` chunk files exceed the
default Lean thread-stack during kernel checking.

Toolchain: `leanprover/lean4:v4.27.0`, Mathlib pinned at `a3a10db0`.

## What is *not* here (yet)

A larger development from the same loop claims a kernel-checked verified range
of `M ≤ 5.08×10¹⁹³` (with `n₁ > 6.87×10¹⁹²` and `k > 2.20×10¹⁹³` for any
counterexample), an unconditional residue-class structure theorem
(a counterexample's denominators meet every residue class modulo every
`d ≤ 107`), and a conditional closure from a hypothesis strictly weaker than
the problem page's Sophie-Germain-type condition (anticipated informally in a
May 2026 comment by Woett on the problem page, which should be credited). Those
proof chains run through ~250MB of Lucas primality-certificate files that have
**not yet been independently re-verified**; they are deliberately excluded from
this repository until they have been. This repo contains only what has been
rebuilt from source end-to-end on independent hardware.

## License

Apache 2.0. If you use this, a link to this repository is appreciated.
