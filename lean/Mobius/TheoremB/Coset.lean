import Mobius.Spectral.Modulation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Theorem B, the algebraic core: coset support (Lemma 5.1(c))

The Theorem-B analogue of the Partner Lemma.  Where `partner` exploits the
square-vanishing `μ(q²n)=0`, Theorem B exploits the **sign relation**
`μ(qn) = -μ(n)`: for a usable prime `q` the exponential polynomial
`D_n = â_{qn} + â_n` (frequencies in `B ∪ B�q`) vanishes off the progression `qℤ`.
`coset_support` is the resulting structural fact:

> a nonzero exponential polynomial `D = ∑_{γ∈G} ψ γ` that vanishes off `qℤ` has a
> frequency support `G` that is a union of full cosets of the `q`-th roots of
> unity `U_q`; hence `q ≤ |G|`.

## The mechanism (slicker than the paper's character sum)

The paper argues via the averaging identity `(1/q)∑_j ζ^{jn} = 1_{q∣n}`.  We use
the equivalent **modulation fixed point**: let `T_ζ = modul ζ` (multiply by `ζⁿ`).

* `D` vanishes off `qℤ`  ⟺  `T_{ζ'} D = D` for every `ζ'` with `ζ'^q = 1`
  (pointwise: `q ∣ n ⟹ ζ'ⁿ = 1`; `q ∤ n ⟹ D n = 0`).  No character sum.
* `T_{ζ'}` scales frequencies (`modul_genEigenspace`: `γ ↦ ζ'γ`).  So the
  `η`-component of `T_{ζ'} D` comes from the frequency `ζ'⁻¹η`.  If `ζ'⁻¹η ∉ G`
  then `T_{ζ'} D = D` has *no* `η`-component, forcing `ψ η = 0` by generalized
  **eigenspace independence** — the same `Module.End.independent_genEigenspace`
  that drives `partner`.  Contrapositive: `η ∈ G ⟹ ζ'⁻¹η ∈ G` (coset closure).
* Closure + a primitive `q`-th root give a `q`-element orbit `{ζⁱγ₀}` inside `G`.

Like `partner`/`entropy_bound`, this stays at the spectral-data abstraction level:
the "vanishes off `qℤ`" hypothesis (the paper's Lemma 5.1(a), the sign-relation
promotion — a `eq_zero_of_consecutive_vanish` argument) and `G.Nonempty` (Lemma
5.1(b), the Bertrand nontriviality) are taken as given, since the tree carries no
`μ`.  `IsPrimitiveRoot ζ q` in characteristic `p` already forces `p ∤ q`.

The passage to `L ≥ c·√(N/log N)` (Theorem `thm:sqrt`) needs the clusters lemma
plus *both* effective prime-counting bounds (`π(x) > x/log x` and
`π(x) < 1.25506 x/log x`) — the deferred analytic layer.
-/

namespace Mobius

variable {k : Type*} [Field k]

/-- **Coset-support bound (Lemma 5.1(c)).**  Let `D = ∑_{γ∈G} ψ γ` be a nonzero
exponential polynomial over `k` (distinct nonzero frequencies `G`, nonzero
components `ψ γ ∈ genEigenspace γ`).  If `D` vanishes at every `n` with `q ∤ n`,
and `ζ` is a primitive `q`-th root of unity, then `q ≤ |G|`. -/
theorem coset_support {q : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ q)
    {G : Finset k} {ψ : k → Seq k}
    (hG0 : ∀ γ ∈ G, γ ≠ 0)
    (hmem : ∀ γ ∈ G, ψ γ ∈ shift.genEigenspace γ ⊤)
    (hne : ∀ γ ∈ G, ψ γ ≠ 0)
    (hoff : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → (∑ γ ∈ G, ψ γ) n = 0)
    (hNE : G.Nonempty) :
    q ≤ G.card := by
  classical
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · simp [hq0]
  · have hζ0 : ζ ≠ 0 := hζ.ne_zero hqpos.ne'
    set D : Seq k := ∑ γ ∈ G, ψ γ with hD
    -- `D` vanishes off `qℤ`  ⟺  `T_ζ' D = D` for every `ζ'` with `ζ'^q = 1`.
    have modul_fix : ∀ ζ' : k, ζ' ^ q = 1 → modul ζ' D = D := by
      intro ζ' hζ'
      funext n
      rw [modul_apply]
      by_cases hqn : (q : ℤ) ∣ n
      · obtain ⟨m, rfl⟩ := hqn
        rw [zpow_mul, zpow_natCast, hζ', one_zpow, one_mul]
      · rw [hoff n hqn, mul_zero]
    -- Coset closure: `η ∈ G ⟹ ζ'⁻¹ η ∈ G`.
    have closure : ∀ ζ' : k, ζ' ≠ 0 → ζ' ^ q = 1 → ∀ η ∈ G, ζ'⁻¹ * η ∈ G := by
      intro ζ' hζ'0 hζ'1 η hη
      by_contra hcon
      -- `D = T_ζ' D` has no `η`-frequency component
      have hD_mem : D ∈ ⨆ (j) (_ : j ≠ η), shift.genEigenspace j ⊤ := by
        rw [← modul_fix ζ' hζ'1, hD, map_sum]
        apply Submodule.sum_mem
        intro γ hγ
        have hγη : ζ' * γ ≠ η := by
          intro h
          apply hcon
          rw [← h, ← mul_assoc, inv_mul_cancel₀ hζ'0, one_mul]
          exact hγ
        exact Submodule.mem_iSup_of_mem (ζ' * γ)
          (Submodule.mem_iSup_of_mem hγη (modul_genEigenspace hζ'0 (hmem γ hγ)))
      -- the `η`-term is isolated: it lies in `genEigenspace η ⊓ ⨆_{j≠η} = 0`
      have htail_mem : (∑ γ ∈ G.erase η, ψ γ)
          ∈ ⨆ (j) (_ : j ≠ η), shift.genEigenspace j ⊤ := by
        apply Submodule.sum_mem
        intro γ hγ
        exact Submodule.mem_iSup_of_mem γ
          (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hγ)
            (hmem γ (Finset.mem_of_mem_erase hγ)))
      have hψη : ψ η = D - ∑ γ ∈ G.erase η, ψ γ := by
        rw [hD, ← Finset.add_sum_erase _ _ hη]; ring
      have hψη_mem : ψ η ∈ ⨆ (j) (_ : j ≠ η), shift.genEigenspace j ⊤ := by
        rw [hψη]; exact Submodule.sub_mem _ hD_mem htail_mem
      have hdisj := (iSupIndep_def.mp (Module.End.independent_genEigenspace shift ⊤)) η
      exact hne η hη ((Submodule.disjoint_def.mp hdisj) _ (hmem η hη) hψη_mem)
    -- Closure under `·ζ` (apply closure with `ζ⁻¹`).
    have hζinv1 : (ζ⁻¹) ^ q = 1 := by rw [inv_pow, hζ.pow_eq_one, inv_one]
    have step : ∀ η ∈ G, ζ * η ∈ G := by
      intro η hη
      have h := closure ζ⁻¹ (inv_ne_zero hζ0) hζinv1 η hη
      rwa [inv_inv] at h
    -- The orbit `{ζⁱ γ₀ : i < q}` lies in `G`, and has `q` distinct elements.
    obtain ⟨γ₀, hγ₀⟩ := hNE
    have orbit : ∀ i : ℕ, ζ ^ i * γ₀ ∈ G := by
      intro i
      induction i with
      | zero => simpa using hγ₀
      | succ i ih =>
          have h := step _ ih
          rwa [← mul_assoc, ← pow_succ'] at h
    have hsub : (Finset.range q).image (fun i => ζ ^ i * γ₀) ⊆ G := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact orbit i
    have hInj : Set.InjOn (fun i => ζ ^ i * γ₀) ↑(Finset.range q) :=
      hζ.injOn_pow_mul (hG0 γ₀ hγ₀)
    calc q = ((Finset.range q).image (fun i => ζ ^ i * γ₀)).card := by
              rw [Finset.card_image_of_injOn hInj, Finset.card_range]
      _ ≤ G.card := Finset.card_le_card hsub

-- Sorry-free (only `propext, Classical.choice, Quot.sound`).
#print axioms coset_support

end Mobius
