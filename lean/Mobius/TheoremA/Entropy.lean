import Mobius.Partner
import Mobius.TheoremA.Induction

/-!
# Theorem A, the algebraic core: the entropy bound (§4 assembly)

Combining the **Partner Lemma** (`partner`, over the field `k`) with the
**product-space induction** (`product_space_induction`, over a commutative group)
yields the algebraic heart of the Main Theorem:
```
2 ^ |P| ≤ |B|
```
for `P` any set of "usable" primes (each `q ∈ P` prime, `q ≠ p`, with the
square-vanishing `decim (q²) Φ = 0`) and `B` the frequency set of a *nontrivial*
square-vanishing exponential polynomial `Φ = ∑_{β ∈ B} φ β`.

This is the paper's `L ≥ r ≥ 2^{π(Q₀)-1}` (Theorem `thm:main`), with `|P|` in the
role of `π(Q₀)-1`.  The remaining passage to `c·N/(log N·log log N)²` is the
analytic layer (`π(x) > x/log x`, Rosser–Schoenfeld), deferred — see the closing
note in `Mobius/TheoremA/Induction.lean`.

## The bridge `B ⊆ k  ↪  kˣ`

`partner` gives, for each usable `q`, a partner `β' ∈ B` with `β'^{q²} = β^{q²}`
in `k`.  `product_space_induction` wants, in a *group*, a companion `s'` with
`s'/s` in the `q`-primary component.  The two meet in the unit group `kˣ`: the
nonzero `β ∈ B` lift to units `toU β := Units.mk0 β`, and `β'^{q²} = β^{q²}`
becomes `(toU β' / toU β)^{q²} = 1`, i.e. `toU β' / toU β ∈ primaryComponent kˣ q`
(order dividing `q²`, a `q`-power).  Injectivity of the lift preserves cardinality,
so `2^{|P|} ≤ |B'| = |B|`.

`B.Nonempty` is the paper's nontriviality `r ≥ 1`: it is genuinely needed, since a
`B = ∅` satisfies `hvanish` vacuously while `2^{|P|} ≤ 0` is false.
-/

namespace Mobius

open CommGroup

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p]

/-- **Theorem A, algebraic core (the entropy bound).**  Let `Φ = ∑_{β ∈ B} φ β` be
a nontrivial exponential polynomial over `k` (distinct nonzero frequencies `B`,
nonzero components `φ β ∈ genEigenspace β`).  If for every prime `q` in a set `P`
of primes `≠ p` the `q²`-decimation of `Φ` vanishes, then `2^{|P|} ≤ |B|`. -/
theorem entropy_bound
    {B : Finset k} {φ : k → Seq k} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime)
    (hqp : ∀ q ∈ P, ¬ p ∣ q)
    (hB0 : ∀ β ∈ B, β ≠ 0)
    (hBne : B.Nonempty)
    (hmem : ∀ β ∈ B, φ β ∈ shift.genEigenspace β ⊤)
    (hne : ∀ β ∈ B, φ β ≠ 0)
    (hvanish : ∀ q ∈ P, decim (q ^ 2) (∑ β ∈ B, φ β) = 0) :
    2 ^ P.card ≤ B.card := by
  classical
  -- Lift the nonzero frequencies `B ⊆ k` to units of `k`.
  let toU : {a // a ∈ B} → kˣ := fun x => Units.mk0 (x : k) (hB0 (x : k) x.2)
  have htoU_val : ∀ x : {a // a ∈ B}, (toU x : k) = (x : k) := fun _ => rfl
  have htoU_inj : Function.Injective toU := by
    intro a b hab
    apply Subtype.ext
    rw [← htoU_val a, ← htoU_val b, hab]
  -- The lift preserves cardinality.
  have hcard : (B.attach.image toU).card = B.card := by
    rw [Finset.card_image_of_injective _ htoU_inj, Finset.card_attach]
  -- … and nonemptiness.
  have hne' : (B.attach.image toU).Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨toU ⟨b, hb⟩, Finset.mem_image_of_mem toU (Finset.mem_attach _ _)⟩
  -- The Partner Lemma, transported into `kˣ`: every image point has, for each
  -- usable prime `q`, a distinct `q`-primary companion.
  have hpartner : ∀ s ∈ B.attach.image toU, ∀ q ∈ P,
      ∃ s' ∈ B.attach.image toU, s' ≠ s ∧ s' / s ∈ primaryComponent kˣ q := by
    intro s hs q hq
    rw [Finset.mem_image] at hs
    obtain ⟨x, -, rfl⟩ := hs
    obtain ⟨β', hβ'B, hβ'ne, hβ'pow⟩ :=
      partner hB0 hmem hne (hqp q hq) (hvanish q hq) (x : k) x.2
    refine ⟨toU ⟨β', hβ'B⟩,
      Finset.mem_image_of_mem toU (Finset.mem_attach _ _), ?_, ?_⟩
    · -- distinctness: `β' ≠ β` lifts through the injective `toU`
      intro heq
      exact hβ'ne (congrArg Subtype.val (htoU_inj heq))
    · -- `q`-primary: `(toU β' / toU β)^{q²} = 1`
      rw [mem_primaryComponent]
      refine ⟨2, ?_⟩
      have hpow_eq : (toU ⟨β', hβ'B⟩) ^ (q ^ 2) = (toU x) ^ (q ^ 2) := by
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, htoU_val]
        exact hβ'pow
      rw [div_pow, hpow_eq, div_self']
  -- Feed the induction and rewrite `|B'| = |B|`.
  have h := product_space_induction P hP (B.attach.image toU) hne' hpartner
  rwa [hcard] at h

-- Sorry-free (only `propext, Classical.choice, Quot.sound`).
#print axioms entropy_bound

end Mobius
