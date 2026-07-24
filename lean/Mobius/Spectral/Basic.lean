import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.Torsion.Field

/-!
# Basic setup: sequences, the shift, decimation, generalized eigenspaces

Formalization of the machinery behind the **Partner Lemma** (Lemma 3.4) of
*"Near-linear lower bounds for the N-th linear complexity of the Möbius
function"*.

We model bi-infinite sequences over a field `k` as the `k`-module `Seq k := ℤ → k`.
The **shift** `S` with `(S u) n = u (n+1)` is a `k`-linear automorphism; the paper's
"exponential polynomial with single frequency `β`" is exactly a generalized
eigenvector of `S` for the eigenvalue `β`, i.e. an element of
`S.genEigenspace β ⊤ = {u | ∃ l, (S - β)^l u = 0}`.

**Decimation** `decim d` with `(decim d u) n = u (d n)` is the other operator the
Partner Lemma manipulates: `decim d u = 0` says precisely that `u` vanishes on the
arithmetic progression `d ℤ`.  The square-vanishing of `μ` (`μ(q²n) = 0`) enters
the argument as `decim (q²) Φ = 0`.

Everything here is over an *arbitrary* field `k` of characteristic `p`; the paper's
`k = 𝔽̄_p` is one instance (see `Mobius/Partner.lean` for the specialization).
-/

namespace Mobius

open Polynomial

variable (k : Type*) [Field k]

/-- Bi-infinite sequences over `k`, the ambient `k`-module. -/
abbrev Seq := ℤ → k

variable {k}

/-- The shift endomorphism, `(S u) n = u (n + 1)`. -/
def shift : Module.End k (Seq k) where
  toFun u := fun n => u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma shift_apply (u : Seq k) (n : ℤ) : shift u n = u (n + 1) := rfl

/-- Decimation by `d`: `(decim d u) n = u (d n)`.  Then `decim d u = 0` iff `u`
vanishes on `d ℤ`. -/
def decim (d : ℕ) : Module.End k (Seq k) where
  toFun u := fun n => u ((d : ℤ) * n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma decim_apply (d : ℕ) (u : Seq k) (n : ℤ) :
    decim d u n = u ((d : ℤ) * n) := rfl

/-- Iterating the shift `j` times reads the sequence `j` steps ahead. -/
lemma shift_pow_apply (j : ℕ) (u : Seq k) (n : ℤ) : (shift ^ j) u n = u (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, shift_apply, ih]
      congr 1
      push_cast; ring

/-- The key intertwining relation `S * (decim d) = (decim d) * S^d`: shifting a
`d`-decimated sequence by one step is the same as `d`-decimating the sequence
shifted by `d` steps.  This is what forces decimation to send an eigenvalue `β`
to `β^d` (Lemma 3.3 / the Partner Lemma's mechanism). -/
lemma shift_mul_decim (d : ℕ) :
    (shift * decim d : Module.End k (Seq k)) = decim d * shift ^ d := by
  ext u n
  simp only [Module.End.mul_apply, shift_apply, decim_apply, shift_pow_apply]
  congr 1
  ring

end Mobius
