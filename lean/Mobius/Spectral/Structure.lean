import Mobius.Spectral.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr

/-!
# Structure Lemma: the spectral facts behind the Partner Lemma

This file proves the two structural facts the Partner Lemma consumes, over an
arbitrary field `k` of characteristic `p`:

* `decim_genEigenspace` — **decimation shifts frequencies by a power** (part of the
  paper's Lemma 2.1(iv)/3.3 mechanism): if `u` is a generalized eigenvector of the
  shift for eigenvalue `β`, then `decim d u` is one for eigenvalue `β^d`.

* `density` — **the paper's Lemma 2.1(v), the heart of the whole argument**, and
  the *only* place where `q ≠ p` is used:  a generalized eigenvector `u` (nonzero
  frequency `β`) that vanishes on `d ℤ` with `p ∤ d` is identically zero.

The engine of `density` is the characteristic-`p` "freshman's dream"
`(S - β)^{p^t} = S^{p^t} - β^{p^t}` (`shift_sub_smul_char_pow`, from
`sub_pow_char_pow`): it turns a generalized eigenvector into a genuinely
*quasi-periodic* sequence (period `p^t`, ratio `β^{p^t}`), after which vanishing on
`d ℤ` for `d` coprime to `p` propagates to all of `ℤ` by Bézout.  When `q = p` the
identity degenerates (the progression `p² ℤ` is not dense mod `p^t`) and the lemma
genuinely fails — exactly the paper's Remark 3.5.
-/

namespace Mobius

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p]

/-- `(β·1)^n = β^n·1` in the endomorphism algebra (a scalar times the identity). -/
private lemma smul_one_pow (β : k) (n : ℕ) :
    ((β : k) • (1 : Module.End k (Seq k))) ^ n = (β ^ n) • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← map_pow, Algebra.algebraMap_eq_smul_one]

/-- **Freshman's dream for the shift.**  In characteristic `p`,
`(S - β·1)^{p^t} = S^{p^t} - β^{p^t}·1`.  Transported from `(X - Cβ)^{p^t}
= X^{p^t} - C(β^{p^t})` in `k[X]` (`sub_pow_char_pow`) through `aeval S`. -/
lemma shift_sub_smul_char_pow (β : k) (t : ℕ) :
    ((shift - β • 1 : Module.End k (Seq k)) ^ p ^ t)
      = shift ^ p ^ t - (β ^ p ^ t) • 1 := by
  have hpoly : ((X - C β) ^ p ^ t : k[X]) = X ^ p ^ t - C (β ^ p ^ t) := by
    rw [sub_pow_char_pow, ← C_pow]
  have h := congrArg (aeval (shift : Module.End k (Seq k))) hpoly
  simp only [map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
  rw [smul_one_pow] at h
  exact h

/-- Divisibility input to `decim_genEigenspace`: since `(X - β) ∣ (X^d - β^d)`,
a vector killed by `(S - β)^l` is killed by `(S^d - β^d)^l`. -/
private lemma pow_sub_pow_smul_apply_eq_zero {β : k} {u : Seq k} {l d : ℕ}
    (hl : ((shift - β • 1 : Module.End k (Seq k)) ^ l) u = 0) :
    ((shift ^ d - (β ^ d) • 1 : Module.End k (Seq k)) ^ l) u = 0 := by
  obtain ⟨g, hg⟩ : (X - C β) ∣ (X ^ d - C (β ^ d)) := by
    have h := sub_dvd_pow_sub_pow (X : k[X]) (C β) d
    rwa [← C_pow] at h
  have hg' : (X ^ d - C (β ^ d) : k[X]) = g * (X - C β) := by rw [hg]; ring
  have key : (shift ^ d - (β ^ d) • 1 : Module.End k (Seq k))
           = aeval shift g * (shift - β • 1) := by
    have h := congrArg (aeval (shift : Module.End k (Seq k))) hg'
    simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one] at h
    rw [smul_one_pow] at h
    exact h
  have hcomm : Commute (aeval (shift : Module.End k (Seq k)) g) (shift - β • 1) := by
    have e1 : (shift - β • 1 : Module.End k (Seq k)) = aeval shift (X - C β) := by
      simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [e1]
    exact (Commute.all g (X - C β)).map (aeval shift)
  rw [key, hcomm.mul_pow, Module.End.mul_apply, hl, map_zero]

/-- **Decimation shifts the frequency by a `d`-th power.**  If `u` lies in the
generalized `β`-eigenspace of the shift, then `decim d u` lies in the generalized
`β^d`-eigenspace.  (This is the identity `Ŝ_{q²n}` lands on frequencies `β^{q²}`,
Lemma 3.3.) -/
lemma decim_genEigenspace {β : k} {u : Seq k} (d : ℕ)
    (hmem : u ∈ shift.genEigenspace β ⊤) :
    decim d u ∈ shift.genEigenspace (β ^ d) ⊤ := by
  rw [Module.End.mem_genEigenspace_top] at hmem ⊢
  obtain ⟨l, hl⟩ := hmem
  rw [LinearMap.mem_ker] at hl
  refine ⟨l, ?_⟩
  rw [LinearMap.mem_ker]
  -- the base semiconjugacy `(S - β^d)·(decim d) = (decim d)·(S^d - β^d)`
  have base : (shift - (β ^ d) • 1 : Module.End k (Seq k)) * decim d
            = decim d * (shift ^ d - (β ^ d) • 1) := by
    have hsc : (shift : Module.End k (Seq k)) * decim d = decim d * shift ^ d :=
      shift_mul_decim d
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hsc]
  have powbase : (shift - (β ^ d) • 1 : Module.End k (Seq k)) ^ l * decim d
               = decim d * (shift ^ d - (β ^ d) • 1) ^ l := by
    have hsemi : SemiconjBy (decim d)
        (shift ^ d - (β ^ d) • 1 : Module.End k (Seq k)) (shift - (β ^ d) • 1) :=
      base.symm
    exact (hsemi.pow_right l).symm
  have hval : ((shift ^ d - (β ^ d) • 1 : Module.End k (Seq k)) ^ l) u = 0 :=
    pow_sub_pow_smul_apply_eq_zero (d := d) hl
  rw [← Module.End.mul_apply, powbase, Module.End.mul_apply, hval, map_zero]

/-- **Lemma 2.1(v) — the density step; the heart of the Partner Lemma.**
A generalized eigenvector `u` of the shift with *nonzero* frequency `β`, vanishing
on the progression `d ℤ` with `p ∤ d`, is identically `0`.

Proof: `shift_sub_smul_char_pow` makes `u` quasi-periodic with period `p^t`
(`u(n+p^t) = β^{p^t} u(n)`); the zero set of `u` is therefore stable under `±p^t`
and contains `d ℤ`; since `gcd(d, p^t) = 1`, Bézout writes every integer as a
`ℤ`-combination of `d` and `p^t`, so the zero set is all of `ℤ`. -/
lemma density {β : k} {u : Seq k} (hβ : β ≠ 0) {d : ℕ} (hd : ¬ p ∣ d)
    (hmem : u ∈ shift.genEigenspace β ⊤) (hvanish : decim d u = 0) : u = 0 := by
  -- some `l` with `(S - β)^l u = 0`
  rw [Module.End.mem_genEigenspace_top] at hmem
  obtain ⟨l, hlmem⟩ := hmem
  rw [LinearMap.mem_ker] at hlmem
  -- a period `p^t ≥ l`
  have hlepow : ∀ m : ℕ, m ≤ p ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h2 : 2 ≤ p := hp.out.two_le
        have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
        calc m + 1 ≤ p ^ m + p ^ m := by omega
          _ = 2 * p ^ m := by ring
          _ ≤ p * p ^ m := by gcongr
          _ = p ^ (m + 1) := by rw [pow_succ]; ring
  obtain ⟨t, ht⟩ : ∃ t : ℕ, l ≤ p ^ t := ⟨l, hlepow l⟩
  -- `u` is killed by `(S - β)^{p^t}`
  have hAu : ((shift - β • 1 : Module.End k (Seq k)) ^ p ^ t) u = 0 := by
    have hsplit : (shift - β • 1 : Module.End k (Seq k)) ^ p ^ t
                = (shift - β • 1) ^ (p ^ t - l) * (shift - β • 1) ^ l := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, Module.End.mul_apply, hlmem, map_zero]
  -- hence quasi-periodic: `S^{p^t} u = β^{p^t} • u`
  have hquasi : (shift ^ p ^ t) u - (β ^ p ^ t) • u = 0 := by
    have h := hAu
    rw [shift_sub_smul_char_pow] at h
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
    exact h
  have hqp : ∀ n : ℤ, u (n + (p ^ t : ℕ)) = (β ^ p ^ t) * u n := by
    intro n
    have h := congrFun hquasi n
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, shift_pow_apply,
      smul_eq_mul] at h
    exact sub_eq_zero.mp h
  have hβP : (β ^ p ^ t) ≠ 0 := pow_ne_zero _ hβ
  -- the zero set of `u` is stable under translation by `p^t · ℤ`
  have hzero : ∀ (x : ℤ), u x = 0 → ∀ (s : ℤ), u (x + (p ^ t : ℕ) * s) = 0 := by
    intro x hx s
    induction s using Int.induction_on with
    | zero => simpa using hx
    | succ i ih =>
        have e : x + (p ^ t : ℕ) * ((i : ℤ) + 1)
               = (x + (p ^ t : ℕ) * (i : ℤ)) + (p ^ t : ℕ) := by ring
        rw [e, hqp, ih, mul_zero]
    | pred i ih =>
        have e : x + (p ^ t : ℕ) * (-(i : ℤ))
               = (x + (p ^ t : ℕ) * (-(i : ℤ) - 1)) + (p ^ t : ℕ) := by ring
        have h := hqp (x + (p ^ t : ℕ) * (-(i : ℤ) - 1))
        rw [← e, ih] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hβP
  -- Bézout: `d` and `p^t` are coprime
  have hcop : Nat.Coprime d (p ^ t) :=
    (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd).symm).pow_right t
  have hbez : (d : ℤ) * (Nat.gcdA d (p ^ t)) + (p ^ t : ℤ) * (Nat.gcdB d (p ^ t)) = 1 := by
    have h := Nat.gcd_eq_gcd_ab d (p ^ t)
    rw [show Nat.gcd d (p ^ t) = 1 from hcop] at h
    simpa using h.symm
  funext m
  show u m = 0
  have hm : (d : ℤ) * (m * Nat.gcdA d (p ^ t)) + (p ^ t : ℤ) * (m * Nat.gcdB d (p ^ t)) = m := by
    linear_combination m * hbez
  have h0 : u ((d : ℤ) * (m * Nat.gcdA d (p ^ t))) = 0 := by
    simpa [decim_apply] using congrFun hvanish (m * Nat.gcdA d (p ^ t))
  rw [← hm]
  exact hzero ((d : ℤ) * (m * Nat.gcdA d (p ^ t))) h0 (m * Nat.gcdB d (p ^ t))

end Mobius
