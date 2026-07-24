import Mobius.Spectral.Basic
import Mobius.Spectral.Structure

/-!
# The Partner Lemma (Lemma 3.4)

The centerpiece.  Let `Φ = ∑_{β ∈ B} φ β` be an exponential polynomial over a field
`k` of characteristic `p`, with distinct nonzero frequencies `B` and nonzero
components `φ β` (each a generalized eigenvector of the shift for eigenvalue `β`).
If `Φ` vanishes on the progression `q² ℤ` (the promoted square-vanishing of `μ`)
and `p ∤ q`, then **every frequency `β ∈ B` has a partner** `β' ∈ B`, `β' ≠ β`,
with `β'^{q²} = β^{q²}` — i.e. the ratio `β'/β` is a `q²`-th root of unity.

The proof is the paper's, in operator form:

* `decim (q²)` sends the `β`-component into the generalized `β^{q²}`-eigenspace
  (`decim_genEigenspace`);
* the promoted vanishing says these images sum to `0`;
* generalized eigenspaces for **distinct** eigenvalues are independent
  (`independent_genEigenspace`), so if `β` had *no* partner its image would be
  isolated in its own eigenspace, forcing `decim (q²) (φ β) = 0`;
* but then the **density lemma** (`density`, the `q ≠ p` heart) forces `φ β = 0`,
  contradicting nontriviality.

`partner` is proved with **no `sorry`**.  Its single hypothesis
`decim (q²) Φ = 0` is the conclusion of the Promotion Lemma 3.3; that promotion is
the standard finite→infinite propagation (Structure Lemma (iii)), formalized below
as `eq_zero_of_consecutive_vanish` — now **fully proved** (the last `sorry` in the
tree, closed as a two-sided linear recurrence argument).
-/

namespace Mobius

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p]
variable {B : Finset k} {φ : k → Seq k} {q : ℕ}

/-- **The Partner Lemma (Lemma 3.4).**  Every frequency of a square-vanishing
exponential polynomial has a `U_{q²}`-partner. -/
theorem partner
    (hB0 : ∀ β ∈ B, β ≠ 0)
    (hmem : ∀ β ∈ B, φ β ∈ shift.genEigenspace β ⊤)
    (hne : ∀ β ∈ B, φ β ≠ 0)
    (hq : ¬ p ∣ q)
    (hvanish : decim (q ^ 2) (∑ β ∈ B, φ β) = 0) :
    ∀ β ∈ B, ∃ β' ∈ B, β' ≠ β ∧ β' ^ (q ^ 2) = β ^ (q ^ 2) := by
  classical
  have hq2 : ¬ p ∣ q ^ 2 := fun h => hq (hp.out.dvd_of_dvd_pow h)
  -- push the shift-linear `decim` through the finite sum
  have hsum : ∑ β' ∈ B, decim (q ^ 2) (φ β') = 0 := by
    rw [← map_sum]; exact hvanish
  intro β hβ
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- `hcon`: `β` has no partner, i.e. it is the unique element of `B` with its `q²`-power.
  -- Isolate the `β` term of the vanishing sum.
  have hins : ∑ x ∈ insert β (B.erase β), decim (q ^ 2) (φ x)
            = decim (q ^ 2) (φ β) + ∑ x ∈ B.erase β, decim (q ^ 2) (φ x) :=
    Finset.sum_insert (Finset.notMem_erase β B)
  rw [Finset.insert_erase hβ] at hins
  have key0 : decim (q ^ 2) (φ β) + ∑ β' ∈ B.erase β, decim (q ^ 2) (φ β') = 0 := by
    rw [← hins]; exact hsum
  have hdecβ : decim (q ^ 2) (φ β) = - ∑ β' ∈ B.erase β, decim (q ^ 2) (φ β') :=
    eq_neg_of_add_eq_zero_left key0
  -- `decim (q²) (φ β)` lies in the generalized `β^{q²}`-eigenspace …
  have hβ_mem1 : decim (q ^ 2) (φ β) ∈ shift.genEigenspace (β ^ (q ^ 2)) ⊤ :=
    decim_genEigenspace (q ^ 2) (hmem β hβ)
  -- … and (via `hcon`) also in the span of the *other* eigenspaces
  have hsum_mem : (∑ β' ∈ B.erase β, decim (q ^ 2) (φ β'))
      ∈ ⨆ (j) (_ : j ≠ β ^ (q ^ 2)), shift.genEigenspace j ⊤ := by
    apply Submodule.sum_mem
    intro β' hβ'
    have hβ'B := Finset.mem_of_mem_erase hβ'
    have hβ'ne := Finset.ne_of_mem_erase hβ'
    have hmemβ' : decim (q ^ 2) (φ β') ∈ shift.genEigenspace (β' ^ (q ^ 2)) ⊤ :=
      decim_genEigenspace (q ^ 2) (hmem β' hβ'B)
    exact Submodule.mem_iSup_of_mem (β' ^ (q ^ 2))
      (Submodule.mem_iSup_of_mem (hcon β' hβ'B hβ'ne) hmemβ')
  have hβ_mem2 : decim (q ^ 2) (φ β)
      ∈ ⨆ (j) (_ : j ≠ β ^ (q ^ 2)), shift.genEigenspace j ⊤ := by
    rw [hdecβ]; exact Submodule.neg_mem _ hsum_mem
  -- independence of eigenspaces at distinct eigenvalues ⇒ the image is `0`
  have hdisj := (iSupIndep_def.mp (Module.End.independent_genEigenspace shift ⊤)) (β ^ (q ^ 2))
  have hzero : decim (q ^ 2) (φ β) = 0 :=
    (Submodule.disjoint_def.mp hdisj) _ hβ_mem1 hβ_mem2
  -- the density lemma (the `q ≠ p` step) now kills `φ β`
  exact hne β hβ (density (hB0 β hβ) hq2 (hmem β hβ) hzero)

/-- **Partner Lemma, root-of-unity form.**  The partner ratio `β'/β` is a genuine
`q²`-th root of unity, `(β'/β)^{q²} = 1` — the paper's `β'/β ∈ U_{q²}`. -/
theorem partner_ratio
    (hB0 : ∀ β ∈ B, β ≠ 0)
    (hmem : ∀ β ∈ B, φ β ∈ shift.genEigenspace β ⊤)
    (hne : ∀ β ∈ B, φ β ≠ 0)
    (hq : ¬ p ∣ q)
    (hvanish : decim (q ^ 2) (∑ β ∈ B, φ β) = 0) :
    ∀ β ∈ B, ∃ β' ∈ B, β' ≠ β ∧ (β' / β) ^ (q ^ 2) = 1 := by
  intro β hβ
  obtain ⟨β', hβ'B, hne', hpow⟩ := partner hB0 hmem hne hq hvanish β hβ
  refine ⟨β', hβ'B, hne', ?_⟩
  rw [div_pow, hpow, div_self (pow_ne_zero _ (hB0 β hβ))]

/-!
### Promotion (Lemma 3.3) — the propagation step

`partner` consumes `decim (q²) Φ = 0`.  In the paper this is the conclusion of the
**Promotion Lemma 3.3**: the *finite* square-vanishing `μ(q²n) = 0` (valid for `n`
in an explicit window) forces the *all-ℤ* identity, because the `q²`-decimation of
`Φ` solves a recurrence of order `≤ L` and vanishes at `L` consecutive points.

That final propagation is the standard **Structure Lemma (iii)**, proved in full
below (`eq_zero_of_consecutive_vanish`) — the invertibility of the companion (both
the leading and constant coefficients are nonzero) makes the recurrence solvable in
*both* directions, so a window of `deg g` consecutive zeros propagates to all of ℤ.
-/

/-- **Structure Lemma (iii).**  If `u` is annihilated by `g(S)` for a polynomial `g`
with nonzero constant term (invertible companion), and `u` vanishes at `deg g`
consecutive integers, then `u ≡ 0`.  This is the propagation fact behind Promotion
3.3.

Proof: `g(S) u = 0` unfolds to the two-sided linear recurrence
`∑_{i≤d} g.coeff i · u(n+i) = 0` (`hrec`).  Since the leading coefficient
`g.coeff d` is nonzero (`d = deg g`, `g ≠ 0`) the recurrence solves *forward*, and
since `g.coeff 0 ≠ 0` it solves *backward*; so a window of `d` consecutive zeros
propagates in both directions to all of `ℤ`.  The `d = 0` case (`g` a nonzero
constant) is immediate.  Uses only `[Field k]` — no characteristic hypothesis. -/
lemma eq_zero_of_consecutive_vanish {g : k[X]} (hg0 : g.coeff 0 ≠ 0) {u : Seq k}
    (hu : (aeval shift g) u = 0) {a : ℤ}
    (hvan : ∀ i : ℕ, i < g.natDegree → u (a + i) = 0) : u = 0 := by
  classical
  set d := g.natDegree with hd
  have hg_ne : g ≠ 0 := fun h => hg0 (by rw [h, Polynomial.coeff_zero])
  -- The pointwise two-sided recurrence `∑ cᵢ·u(n+i) = 0`.
  have hrec : ∀ n : ℤ, ∑ i ∈ Finset.range (d + 1), g.coeff i * u (n + i) = 0 := by
    intro n
    have hu' : (∑ i ∈ Finset.range (d + 1),
        g.coeff i • (shift : Module.End k (Seq k)) ^ i) u = 0 := by
      rw [← aeval_eq_sum_range]; exact hu
    have h2 := congrFun hu' n
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      shift_pow_apply, smul_eq_mul] using h2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `d = 0`: `g` is a nonzero constant, so `c₀·u(n) = 0` gives `u = 0` directly.
    funext m
    have hr := hrec m
    rw [hd0] at hr
    simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero] at hr
    exact (mul_eq_zero.mp hr).resolve_left hg0
  · -- `d ≥ 1`: propagate the all-zero window forward and backward over ℤ.
    have hlead : g.coeff d ≠ 0 := by
      rw [hd, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hg_ne
    -- window at `a + s` is all zero, by induction on `s`
    have hwin : ∀ s : ℤ, ∀ i ∈ Finset.range d, u (a + s + i) = 0 := by
      intro s
      induction s using Int.induction_on with
      | zero =>
          intro i hi
          simpa using hvan i (Finset.mem_range.mp hi)
      | succ j ih =>
          -- forward: the new top value `u (a + j + d) = 0`
          have hnew : u (a + (j : ℤ) + (d : ℕ)) = 0 := by
            have hr := hrec (a + (j : ℤ))
            rw [Finset.sum_range_succ] at hr
            have hs0 : ∑ i ∈ Finset.range d, g.coeff i * u (a + (j : ℤ) + i) = 0 :=
              Finset.sum_eq_zero fun i hi => by rw [ih i hi, mul_zero]
            rw [hs0, zero_add] at hr
            exact (mul_eq_zero.mp hr).resolve_left hlead
          intro i hi
          rw [Finset.mem_range] at hi
          rcases Nat.lt_or_ge (i + 1) d with h | h
          · have hval := ih (i + 1) (Finset.mem_range.mpr h)
            have e : a + (j : ℤ) + ((i + 1 : ℕ) : ℤ) = a + ((j : ℤ) + 1) + (i : ℤ) := by
              push_cast; ring
            rwa [e] at hval
          · have hid : i + 1 = d := by omega
            have e : a + ((j : ℤ) + 1) + (i : ℤ) = a + (j : ℤ) + ((d : ℕ) : ℤ) := by
              rw [← hid]; push_cast; ring
            rw [e]; exact hnew
      | pred j ih =>
          -- backward: the new bottom value `u (a - j - 1) = 0`
          have hnew : u (a + (-(j : ℤ)) - 1) = 0 := by
            have hr := hrec (a + (-(j : ℤ)) - 1)
            rw [Finset.sum_range_succ'] at hr
            have hs0 : ∑ i ∈ Finset.range d,
                g.coeff (i + 1) * u (a + (-(j : ℤ)) - 1 + ((i + 1 : ℕ) : ℤ)) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              have e : a + (-(j : ℤ)) - 1 + ((i + 1 : ℕ) : ℤ) = a + (-(j : ℤ)) + (i : ℤ) := by
                push_cast; ring
              rw [e, ih i hi, mul_zero]
            rw [hs0, zero_add] at hr
            simpa using (mul_eq_zero.mp hr).resolve_left hg0
          intro i hi
          rw [Finset.mem_range] at hi
          rcases i with _ | ii
          · have e : a + (-(j : ℤ) - 1) + ((0 : ℕ) : ℤ) = a + (-(j : ℤ)) - 1 := by
              push_cast; ring
            rw [e]; exact hnew
          · have hiid : ii < d := by omega
            have hval := ih ii (Finset.mem_range.mpr hiid)
            have e : a + (-(j : ℤ) - 1) + ((ii + 1 : ℕ) : ℤ) = a + (-(j : ℤ)) + (ii : ℤ) := by
              push_cast; ring
            rw [e]; exact hval
    -- conclude: every `m` sits in some window slot `i = 0`
    funext m
    have hval := hwin (m - a) 0 (Finset.mem_range.mpr hdpos)
    have e : a + (m - a) + ((0 : ℕ) : ℤ) = m := by push_cast; ring
    rwa [e] at hval

-- Verification that the Partner Lemma and its whole proof chain are genuinely
-- `sorry`-free: these list only `propext`, `Classical.choice`, `Quot.sound` — and
-- NOT `sorryAx`.  This now includes `eq_zero_of_consecutive_vanish` (the promotion
-- propagation), so the entire file — and the Partner chain — is `sorry`-free.
#print axioms partner
#print axioms partner_ratio
#print axioms density
#print axioms decim_genEigenspace
#print axioms eq_zero_of_consecutive_vanish

end Mobius
