import Mobius.Spectral.Basic

/-!
# Modulation: the frequency-shift operator

The operator behind the **Coset-support Lemma** (Lemma 5.1, Theorem B).  Where
decimation `decim d` sends a frequency `β` to `β^d`, **modulation** `modul ζ` —
pointwise multiplication by the geometric sequence `n ↦ ζⁿ` — sends `β` to `ζβ`:

* `modul ζ : Module.End k (Seq k)`, `(modul ζ u) n = ζⁿ · u n` (a `k`-linear
  automorphism for `ζ ≠ 0`);
* `modul_genEigenspace` — `modul ζ` maps the generalized `β`-eigenspace of the
  shift into the generalized `ζβ`-eigenspace.

This is the exact multiplicative analogue of `decim_genEigenspace`, and it is what
turns "`D` vanishes off the progression `qℤ`" into the fixed-point equation
`modul ζ D = D` for `ζ` a `q`-th root of unity (see `Mobius/TheoremB/Coset.lean`).
Everything here is over an arbitrary field `k`; no characteristic hypothesis.
-/

namespace Mobius

open Polynomial

variable {k : Type*} [Field k]

/-- Modulation by `ζ`: `(modul ζ u) n = ζⁿ · u n`.  A `k`-linear endomorphism of
`Seq k` (an automorphism when `ζ ≠ 0`, with inverse `modul ζ⁻¹`). -/
def modul (ζ : k) : Module.End k (Seq k) where
  toFun u := fun n => ζ ^ n * u n
  map_add' u v := by funext n; simp [mul_add]
  map_smul' c u := by funext n; simp [smul_eq_mul]; ring

@[simp] lemma modul_apply (ζ : k) (u : Seq k) (n : ℤ) : modul ζ u n = ζ ^ n * u n := rfl

/-- **Modulation shifts the frequency by the factor `ζ`.**  If `u` lies in the
generalized `β`-eigenspace of the shift, then `modul ζ u` lies in the generalized
`ζβ`-eigenspace.  (The multiplicative twin of `decim_genEigenspace`.) -/
lemma modul_genEigenspace {ζ β : k} (hζ : ζ ≠ 0) {u : Seq k}
    (hmem : u ∈ shift.genEigenspace β ⊤) :
    modul ζ u ∈ shift.genEigenspace (ζ * β) ⊤ := by
  rw [Module.End.mem_genEigenspace_top] at hmem ⊢
  obtain ⟨l, hl⟩ := hmem
  rw [LinearMap.mem_ker] at hl
  refine ⟨l, ?_⟩
  rw [LinearMap.mem_ker]
  -- base identity: `(S - ζβ)(modul ζ v) = ζ • modul ζ ((S - β) v)`
  have hstep : ∀ v : Seq k,
      (shift - (ζ * β) • 1 : Module.End k (Seq k)) (modul ζ v)
        = ζ • modul ζ ((shift - β • 1 : Module.End k (Seq k)) v) := by
    intro v; funext n
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      shift_apply, modul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [zpow_add_one₀ hζ]; ring
  -- iterate the base identity `l` times, accumulating the scalar `ζ^l`
  have powapp : ∀ (m : ℕ) (v : Seq k),
      ((shift - (ζ * β) • 1 : Module.End k (Seq k)) ^ m) (modul ζ v)
        = ζ ^ m • modul ζ (((shift - β • 1 : Module.End k (Seq k)) ^ m) v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
        intro v
        have hpow : ((shift - β • 1 : Module.End k (Seq k)) ^ m)
              ((shift - β • 1 : Module.End k (Seq k)) v)
            = ((shift - β • 1 : Module.End k (Seq k)) ^ (m + 1)) v := by
          rw [← Module.End.mul_apply, ← pow_succ]
        rw [pow_succ, Module.End.mul_apply, hstep v, map_smul,
          ih ((shift - β • 1 : Module.End k (Seq k)) v),
          smul_smul, ← pow_succ', hpow]
  have hkey := powapp l u
  rw [hl] at hkey
  simpa using hkey

end Mobius
