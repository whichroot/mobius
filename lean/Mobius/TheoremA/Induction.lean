import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Theorem A, §4: the product-space induction (Lemma 4.1)

The combinatorial heart of the entropy bound (Main Theorem).  A finite nonempty set
`S` in a commutative group, in which every element admits, *for each* prime `q` in a
set `P`, a distinct companion whose ratio is `q`-primary, must have
`|S| ≥ 2^{|P|}`.

Applied with `S = B` the Frobenius frequency set (in `k^×`) and `P` the usable
primes: the **Partner Lemma** provides exactly these companions (a ratio in
`U_{q²}` is `q`-primary), so `|B| ≥ 2^{π(Q₀)-1}`.

Proof: induction on `P`.  Quotient by the `q`-primary component `N_q` for the newest
prime `q`; every `q`-partner collapses onto its element (fibres of size `≥ 2`,
giving the factor `2`), while every `q'`-partner (`q' ≠ q`) *survives* the quotient
because primary components at distinct primes are disjoint — so the image still
satisfies the hypothesis and the induction closes.  The induction is over *both* the
prime set and the group (the quotient `G ⧸ N_q` is a new group).

Proved with **no `sorry`**.  (The passage from `2^{π(Q₀)-1}` to the
`N/(log N·log log N)²` bound needs the effective prime-counting lower bound
`π(x) > x/log x`, Rosser–Schoenfeld — not currently in Mathlib; see the closing note.)
-/

namespace Mobius

open CommGroup

/-- Distinct primes have disjoint primary components: an element of both `q`- and
`q'`-power order (with `q ≠ q'` prime) is trivial. -/
private lemma eq_one_of_mem_primaryComponent {G : Type*} [CommGroup G] {q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqq' : q ≠ q') {g : G}
    (hg : g ∈ primaryComponent G q) (hg' : g ∈ primaryComponent G q') : g = 1 := by
  obtain ⟨a, ha⟩ := mem_primaryComponent.mp hg
  obtain ⟨b, hb⟩ := mem_primaryComponent.mp hg'
  have h1 : orderOf g ∣ q ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf g ∣ q' ^ b := orderOf_dvd_of_pow_eq_one hb
  have hcop : Nat.Coprime (q ^ a) (q' ^ b) := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes hq hq').mpr hqq'
  have hdvd : orderOf g ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

/-- Auxiliary form of Lemma 4.1 with the group universally quantified (needed because
the induction step quotients into a new group). -/
private theorem psi_aux : ∀ (P : Finset ℕ), (∀ q ∈ P, q.Prime) →
    ∀ {G : Type*} [CommGroup G] (S : Finset G), S.Nonempty →
      (∀ s ∈ S, ∀ q ∈ P, ∃ s' ∈ S, s' ≠ s ∧ s' / s ∈ primaryComponent G q) →
      2 ^ P.card ≤ S.card := by
  intro P
  induction P using Finset.induction_on with
  | empty => intro _ G _ S hS _; rw [Finset.card_empty, pow_zero]; exact hS.card_pos
  | insert q P' hqP' ih =>
      intro hP G _ S hS hpartner
      classical
      have hqP : q.Prime := hP q (Finset.mem_insert_self q P')
      have hP' : ∀ q' ∈ P', q'.Prime := fun q' hq' => hP q' (Finset.mem_insert_of_mem hq')
      set N : Subgroup G := primaryComponent G q with hN
      set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
      -- the `q`-partner of any `s` maps to the same point under `π`
      have hpair : ∀ s ∈ S, ∃ s' ∈ S, s' ≠ s ∧ π s' = π s := by
        intro s hs
        obtain ⟨s', hs'S, hs'ne, hs'prim⟩ := hpartner s hs q (Finset.mem_insert_self q P')
        refine ⟨s', hs'S, hs'ne, ?_⟩
        have h1 : π (s' / s) = 1 := by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hs'prim
        rw [map_div] at h1
        exact div_eq_one.mp h1
      -- the image `S.image π` inherits the hypothesis for `P'`
      have himg : ∀ t ∈ S.image π, ∀ q' ∈ P',
          ∃ t' ∈ S.image π, t' ≠ t ∧ t' / t ∈ primaryComponent (G ⧸ N) q' := by
        intro t ht q' hq'
        rw [Finset.mem_image] at ht
        obtain ⟨s, hsS, rfl⟩ := ht
        obtain ⟨s', hs'S, hs'ne, hs'prim⟩ := hpartner s hsS q' (Finset.mem_insert_of_mem hq')
        refine ⟨π s', Finset.mem_image_of_mem π hs'S, ?_, ?_⟩
        · -- `π s' ≠ π s`: else `s'/s ∈ N`, but `s'/s` is `q'`-primary, nonzero, `q ≠ q'`
          intro heq
          have hmem : s' / s ∈ N := by
            have h1 : π (s' / s) = 1 := by rw [map_div, heq, div_self']
            rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
            exact h1
          have hqq' : q ≠ q' := fun h => hqP' (h ▸ hq')
          exact hs'ne (div_eq_one.mp
            (eq_one_of_mem_primaryComponent hqP (hP' q' hq') hqq' hmem hs'prim))
        · -- `π s' / π s = π (s'/s)` is `q'`-primary
          rw [← map_div]
          obtain ⟨kk, hkk⟩ := mem_primaryComponent.mp hs'prim
          exact mem_primaryComponent.mpr ⟨kk, by rw [← map_pow, hkk, map_one]⟩
      have hIH : 2 ^ P'.card ≤ (S.image π).card :=
        ih hP' (S.image π) (hS.image π) himg
      -- fibres of `π` on `S` have `≥ 2` elements
      have hfib : 2 * (S.image π).card ≤ S.card := by
        rw [Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem π hx)]
        have hlb : ∀ t ∈ S.image π, 2 ≤ (S.filter (fun x => π x = t)).card := by
          intro t ht
          rw [Finset.mem_image] at ht
          obtain ⟨s, hsS, rfl⟩ := ht
          obtain ⟨s', hs'S, hs'ne, hs'eq⟩ := hpair s hsS
          have hsub : ({s, s'} : Finset G) ⊆ S.filter (fun x => π x = π s) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hsS, rfl⟩
            · exact Finset.mem_filter.mpr ⟨hs'S, hs'eq⟩
          calc 2 = ({s, s'} : Finset G).card := (Finset.card_pair (Ne.symm hs'ne)).symm
            _ ≤ _ := Finset.card_le_card hsub
        calc 2 * (S.image π).card
            = ∑ _t ∈ S.image π, 2 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          _ ≤ ∑ t ∈ S.image π, (S.filter (fun x => π x = t)).card := Finset.sum_le_sum hlb
      -- combine
      rw [Finset.card_insert_of_notMem hqP', pow_succ]
      calc 2 ^ P'.card * 2 ≤ (S.image π).card * 2 := by gcongr
        _ = 2 * (S.image π).card := Nat.mul_comm _ _
        _ ≤ S.card := hfib

/-- **Lemma 4.1 (product-space induction).**  If every element of a finite nonempty
`S ⊆ G` has, for each prime `q ∈ P`, a distinct `q`-primary companion, then
`2^{|P|} ≤ |S|`. -/
theorem product_space_induction {G : Type*} [CommGroup G] (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (S : Finset G) (hS : S.Nonempty)
    (hpartner : ∀ s ∈ S, ∀ q ∈ P, ∃ s' ∈ S, s' ≠ s ∧ s' / s ∈ primaryComponent G q) :
    2 ^ P.card ≤ S.card :=
  psi_aux P hP S hS hpartner

-- Sorry-free (only `propext, Classical.choice, Quot.sound`).
#print axioms product_space_induction

/-!
### The analytic boundary of Theorem A

`product_space_induction` gives `|B| ≥ 2^{|P|}` for `P` the usable primes.  Feeding
it the Partner Lemma yields `L ≥ 2^{π(Q₀)-1}`.  Turning that into the stated
`L ≥ c·N/(log N·log log N)²` requires the *effective* prime-counting lower bound
`π(x) > x/log x` for `x ≥ 17` (Rosser–Schoenfeld), which Mathlib does not currently
provide (it has `Nat.primeCounting` and Chebyshev-type material, but not this
effective constant).  That step is the honest analytic boundary of formalizing
Theorem A in full; the combinatorial content above is complete and `sorry`-free.
-/

end Mobius
