import Mobius.Spectral.Basic
import Mobius.Spectral.Structure
import Mobius.Spectral.Modulation
import Mobius.Partner
import Mobius.TheoremA.Induction
import Mobius.TheoremA.Entropy
import Mobius.TheoremB.Coset

/-!
# Möbius linear-complexity paper — Lean 4 / Mathlib formalization

Formalization of results from *"Near-linear lower bounds for the N-th linear
complexity of the Möbius function"* (the `.tex`/`.pdf` in the parent folder).

## Status (as of this checkpoint)

Toolchain: Lean `v4.31.0`, Mathlib pinned to `v4.31.0` (see `lakefile.toml`).
Build + verify:  `export PATH="$HOME/.elan/bin:$PATH" && lake build`
Every result below is checked `sorry`-free by `#print axioms` (emitted on build);
they depend only on `propext, Classical.choice, Quot.sound`.  **The entire tree is
now `sorry`-free** — the last scaffold (`eq_zero_of_consecutive_vanish`) is closed.

### Proved, `sorry`-free
* `Mobius/Spectral/Basic.lean`      — the shift `S` and decimation `decim d` on
  `Seq k = ℤ → k`, as `k`-linear endomorphisms; `shift_mul_decim` (S·decim = decim·Sᵈ).
* `Mobius/Spectral/Structure.lean`  — the **Structure Lemma**:
    - `shift_sub_smul_char_pow`  freshman's dream `(S-β)^{pᵗ} = S^{pᵗ} - β^{pᵗ}`;
    - `decim_genEigenspace`      decimation sends frequency `β` to `βᵈ`;
    - `density`  **(the `q ≠ p` heart, §2 Lemma 2.1(v))** — a generalized
      eigenvector vanishing on `dℤ` with `p ∤ d` is `0`.
* `Mobius/Spectral/Modulation.lean`  — `modul ζ` (multiply by `ζⁿ`) and
  `modul_genEigenspace`: modulation sends frequency `β` to `ζβ` (the multiplicative
  twin of `decim_genEigenspace`).  The operator behind Theorem B.
* `Mobius/Partner.lean`             — **`partner` (Lemma 3.4, the Partner Lemma)**
  and `partner_ratio` (`(β'/β)^{q²}=1`).  Over an arbitrary field `k` of char `p`.
* `Mobius/TheoremA/Induction.lean`  — **`product_space_induction` (Lemma 4.1)**:
  the entropy/product-space bound `2^{|P|} ≤ |S|`.
* `Mobius/TheoremA/Entropy.lean`     — **`entropy_bound` (Theorem A, algebraic
  core)**: the §4 assembly.  Lifts the frequency set `B ⊆ k` into `kˣ` and feeds
  `partner` into `product_space_induction` to conclude `2^{|P|} ≤ |B|` for `P` the
  usable primes (the paper's `L ≥ r ≥ 2^{π(Q₀)-1}`).  `sorry`-free.
* `eq_zero_of_consecutive_vanish` (in `Partner.lean`) — **Structure Lemma (iii)**,
  the finite→infinite propagation behind Promotion (3.3), now **fully proved**: the
  two-sided linear recurrence `∑ cᵢ·u(n+i)=0` is solvable both forward (leading
  coeff ≠ 0) and backward (constant coeff ≠ 0), so `deg g` consecutive zeros
  propagate to all of ℤ.  Over an arbitrary `[Field k]` (no characteristic
  hypothesis).  `partner` never depended on it, so nothing downstream changed.
* `Mobius/TheoremB/Coset.lean`       — **`coset_support` (Lemma 5.1(c), Theorem B's
  algebraic core)**: a nonzero exponential polynomial `D = ∑_{γ∈G} ψ γ` vanishing
  off `qℤ` has `U_q`-coset-closed frequency support, so `q ≤ |G|`.  Proved via the
  modulation fixed point `T_ζ D = D` + eigenspace independence (the `partner`
  mechanism), then a `q`-element orbit `{ζⁱγ₀}` from `IsPrimitiveRoot ζ q`.

## Roadmap (next windows)
1. ~~**Entropy assembly**~~ — **DONE** (`Mobius/TheoremA/Entropy.lean`,
   `entropy_bound`): `B ⊆ k` lifted into `kˣ`, `partner` + `product_space_induction`
   combined to `2^{|P|} ≤ |B|` (Theorem A's algebraic core, the paper's
   `2^{π(Q₀)-1}`).  `sorry`-free; does not touch the scaffold below.
2. ~~**Finish the scaffold**~~ — **DONE** (`eq_zero_of_consecutive_vanish`): the
   Partner chain — and the whole tree — is now 100% `sorry`-free.
3. **Theorem B** (`√(N/log N)`) — algebraic core **DONE** (`coset_support`, the
   `U_q`-coset structure giving `q ≤ |supp D|`).  Remaining: `lem:clusters` (extract
   near-disjoint `S_q ⊆ B`, `|S_q| ≥ q/2`) and the analytic `thm:sqrt` assembly.

## Known analytic boundary
Theorem A's final `N/(log N·log log N)²` bound needs an effective prime-counting
lower bound of the shape `π(x) ≥ c·x/log x`.  The *textbook* input is Rosser–
Schoenfeld's `π(x) > x/log x` (constant `1`, `x ≥ 17`), which requires effective PNT
(complex analysis + explicit zero-free regions) and is not in Mathlib — PNT itself
lives outside mainline.  **But** Mathlib *does* ship `Chebyshev.pi_ge`, an elementary
lower bound with constant `log 2 ≈ 0.693`; since the endgame only needs
`π(Q₀) ≥ log₂N + O(1)`, a weaker constant merely inflates `Q₀` by a constant factor
and degrades the final `c` — the `N/(log N·log log N)²` *shape* survives.  So the
quantitative statement looks reachable with existing Mathlib (labor, not a missing
prerequisite); this is a conjecture, not yet formalized.  All *algebraic* content is
done.

Theorem B's `√(N/log N)` bound (`thm:sqrt`) sits further behind the same wall: it
uses *both* the effective lower bound and the upper bound `π(x) < 1.25506 x/log x`
(and their dyadic difference `π(2x)-π(x) > 0.56 x/log x`).  Mathlib has an upper
bound too (`Chebyshev.pi_le_log4_mul_div`, constant `log 4 ≈ 1.386`), but combining
the elementary two-sided constants through the dyadic estimate is more delicate — a
separate, larger analytic exercise than Theorem A's.  Its algebraic core
(`coset_support`) is done.
-/
