import Mathlib

/-!
# Finite spectral probes for the local extremal problem

This file is an *experimental, certified search harness* for Problem 8.2 of the
Möbius linear-complexity paper: determine the minimum number `loc(q)` of
frequencies in a nonzero exponential polynomial satisfying

* `u (q * n) = -u n` when `q ∤ n`,
* `u (q^2 * n) = 0`,
* `u (q * n') ≠ 0` for some `n'`.

The unrestricted problem is over an algebraic closure and is not finite.  The
probe below searches the meaningful finite subclass of **constant-coefficient,
`T`-periodic spectral witnesses**

`u(n) = ∑ i, cᵢ * ζ^(xᵢ n)`,

where `ζ` is intended to be a primitive `T`-th root of unity, the exponents
`xᵢ` are distinct, and every coefficient `cᵢ` is nonzero.  A positive result is
a genuine periodic witness with exactly the displayed number of spectral terms
(assuming the usual primitive-root independence).  A negative result excludes
only this bounded periodic search space; it is evidence, not a proof of the
unrestricted lower bound.

The checker is reflected: `hasPeriodicWitness ... = true` is equivalent to the
existence of data satisfying the stated finite relations.  Thus search results
are kernel-checked rather than trusted output from an external program.
-/

namespace Mobius.LocalProbe

open scoped BigOperators

/-- Multiplication by `a` on the residue set `Fin T`. -/
def mulResidue (T a : ℕ) (hT : 0 < T) (n : Fin T) : Fin T :=
  ⟨(a * n.val) % T, Nat.mod_lt _ hT⟩

/-- A constant-coefficient periodic exponential sum.

`xs i` is the exponent of the frequency `ζ`, and `cs i` is its coefficient.
The value only depends on the residue `n : Fin T` when `ζ^T = 1`. -/
def periodicExp {k : Type*} [CommRing k] {T r : ℕ}
    (ζ : k) (xs : Fin r → Fin T) (cs : Fin r → k) (n : Fin T) : k :=
  ∑ i : Fin r, cs i * ζ ^ ((xs i).val * n.val)

/-- The finite local-model constraints for an `r`-frequency, `T`-periodic
spectral candidate.

For mathematical interpretation one should additionally have:

* `q ∣ T`, so divisibility by `q` is well-defined on residue classes;
* `IsPrimitiveRoot ζ T`;
* the characteristic of `k` does not divide `T`.

Those hypotheses are intentionally not needed by the executable checker itself.
They are facts about how a successful finite candidate embeds into the paper's
spectral model. -/
def LocalSpectralCandidate {k : Type*} [CommRing k]
    (q T r : ℕ) (hT : 0 < T) (ζ : k)
    (xs : Fin r → Fin T) (cs : Fin r → k) : Prop :=
  Function.Injective xs ∧
  (∀ i, cs i ≠ 0) ∧
  (∀ n : Fin T,
    periodicExp ζ xs cs (mulResidue T (q ^ 2) hT n) = 0) ∧
  (∀ n : Fin T, ¬ q ∣ n.val →
    periodicExp ζ xs cs (mulResidue T q hT n) =
      -periodicExp ζ xs cs n) ∧
  (∃ n : Fin T,
    periodicExp ζ xs cs (mulResidue T q hT n) ≠ 0)

/-- `LocalSpectralCandidate` is an opaque definition, so Lean will not unfold it
while synthesizing a decision procedure.  Register the finite, computable
instance explicitly. -/
instance instDecidableLocalSpectralCandidate
    {k : Type*} [CommRing k] [DecidableEq k]
    (q T r : ℕ) (hT : 0 < T) (ζ : k)
    (xs : Fin r → Fin T) (cs : Fin r → k) :
    Decidable (LocalSpectralCandidate q T r hT ζ xs cs) := by
  unfold LocalSpectralCandidate
  infer_instance

/-- Exhaustively search all ordered exponent lists and coefficient lists.

The injectivity and nonzero-coefficient clauses remove repetitions and padded
supports.  Ordered lists intentionally duplicate each support by `r!`; this
keeps the checker simple.  For larger searches, symmetry breaking is the first
optimization to add. -/
def hasPeriodicWitness {k : Type*} [CommRing k] [Fintype k] [DecidableEq k]
    (q T r : ℕ) (hT : 0 < T) (ζ : k) : Bool :=
  decide (∃ xs : Fin r → Fin T, ∃ cs : Fin r → k,
    LocalSpectralCandidate q T r hT ζ xs cs)

/-- The Boolean search has no untrusted gap: `true` means that actual spectral
data satisfying `LocalSpectralCandidate` exist. -/
theorem hasPeriodicWitness_eq_true_iff
    {k : Type*} [CommRing k] [Fintype k] [DecidableEq k]
    (q T r : ℕ) (hT : 0 < T) (ζ : k) :
    hasPeriodicWitness q T r hT ζ = true ↔
      ∃ xs : Fin r → Fin T, ∃ cs : Fin r → k,
        LocalSpectralCandidate q T r hT ζ xs cs := by
  simp [hasPeriodicWitness]

/-- Search for a witness with *at most* `R` terms.  Unlike the first version of
this file, this really searches every exact support size `0, …, R`; checking
`hasPeriodicWitness ... R` alone only checks exact size `R`. -/
def periodicUpperBound {k : Type*} [CommRing k] [Fintype k] [DecidableEq k]
    (q T R : ℕ) (hT : 0 < T) (ζ : k) : Bool :=
  decide (∃ r : Fin (R + 1),
    hasPeriodicWitness q T r.val hT ζ = true)

/-! ## Small certified probes

These examples serve two purposes:

1. They regression-test the checker against a case whose principal-class answer
   is known.
2. The period-8 test probes beyond the principal period `q^2 = 4` for `q = 2`.

The `native_decide` proofs are optional in a normal build; moving this file into
an `Experimental` directory keeps the exhaustive computations off the main
import path.
-/

section Q2

/-- For `q = 2`, period `4`, and `𝔽₅` with primitive fourth root `2`, no
candidate with at most three frequencies exists. -/
example : periodicUpperBound (k := ZMod 5) 2 4 3 (by omega) 2 = false := by
  native_decide

/-- The known four-frequency witness at period `4`. -/
def q2T4Exponents : Fin 4 → Fin 4 := fun i => i

def q2T4Coeffs : Fin 4 → ZMod 5 := ![1, 1, 2, 1]

example : LocalSpectralCandidate 2 4 4 (by omega) (2 : ZMod 5)
    q2T4Exponents q2T4Coeffs := by
  native_decide

/-- A non-principal-period probe: over `𝔽₁₇`, `2` has order `8`.  Among
period-8 constant-coefficient spectral sums, there is no witness with at most
three frequencies. -/
example : periodicUpperBound (k := ZMod 17) 2 8 3 (by omega) 2 = false := by
  native_decide

/-- A four-frequency period-8 witness.  Its time-domain values are the period-4
pattern `(0, -1, 1, -1)` repeated; its nonzero Fourier exponents are
`0, 2, 4, 6`. -/
def q2T8Exponents : Fin 4 → Fin 8 := ![0, 2, 4, 6]

def q2T8Coeffs : Fin 4 → ZMod 17 := ![4, 4, 5, 4]

example : LocalSpectralCandidate 2 8 4 (by omega) (2 : ZMod 17)
    q2T8Exponents q2T8Coeffs := by
  native_decide

end Q2

/-!
## Suggested next probes

For a prime `q`, choose `T` divisible by `q^2` and a finite field containing a
primitive `T`-th root `ζ`.  Then evaluate, for increasing `r`,

```
#eval hasPeriodicWitness q T r (by omega) ζ
```

or search all exact sizes through `R` with

```
#eval periodicUpperBound q T R (by omega) ζ
```

The search is exponential in `r`, roughly `(T * |k|)^r`.  Useful next steps are:

* quotient exponent tuples by permutation;
* normalize one coefficient to `1` (global scalar invariance);
* replace coefficient enumeration by a certified row-reduction/nullspace test;
* search several periods `T = q^2, q^3, ...`;
* export any found witness as explicit Lean data and prove it with
  `native_decide`, as above.

A negative result at several periods does **not** settle `loc(q)`: the open
problem permits nonperiodic generalized-eigenvector components.  To turn these
searches into an unrestricted lower bound, one would need a new reduction
showing that an extremizer may be taken in a finite periodic class—or another
finite certificate covering polynomial coefficient functions.
-/

end Mobius.LocalProbe
