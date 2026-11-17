import Mathlib
import RuleHRelease.Definitions.CofactorPaths
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.C_local (N p j : ℕ) (hN : 0 < N) (hp : 0 < p)
    (s : ℤ) (hs : s = ((j / p : ℕ) : ℤ))
    (J : List ℕ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid)
    (hsize : (slot.size : ℤ) ≤ s)
    (r : DivisorGraphRuleH.Route)
    (hfound : DivisorGraphRuleH.SearchReturns J s slot r) :
    (DivisorGraphRuleH.framedBlock slot N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).IsChain
        DivisorGraphRuleH.Comparable ∧
    (DivisorGraphRuleH.scaledCofactors N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).Nodup ∧
    (∀ t ∈ DivisorGraphRuleH.scaledCofactors N p
        (⟨J, r⟩ : DivisorGraphRuleH.TableBlock),
      p * N ∣ t ∧ t ≤ N * j) ∧
    (DivisorGraphRuleH.scaledCofactors N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).length =
        J.length + DivisorGraphRuleH.linkCount r ∧
    J.length + DivisorGraphRuleH.linkCount r =
      1 + DivisorGraphRuleH.gain J r := by
  rcases H3 J s hJ slot hslot hsize r hfound with
    ⟨hroute, hcof, hbound, _hmem, _hx, _hy, _hxy, hend, _hxc, _hyc⟩
  rcases hend with ⟨first, last, hfirst, hlast, hfirstdvd, hlastdvd⟩
  rcases H1 J s hJ r.u r.w hroute.1 hroute.2.1 hroute.2.2.1 hroute.2.2.2 with
    ⟨_hi, _hh, _hl, _hc, _hp, _hf, _he, hperm⟩
  have hlen : (cofactors J r).length = J.length + linkCount r := by
    simp only [cofactors, List.length_append, linkCount, hperm.length_eq]
    omega
  have hscale : ∀ a b : ℕ, a ∣ b → (p * N) * a ∣ (p * N) * b := by
    intro a b hab
    rcases hab with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [hk, Nat.mul_assoc]
  have hscaledChain :
      ((cofactors J r).map (fun c => (p * N) * c)).IsChain Comparable := by
    apply List.isChain_map_of_isChain (fun c => (p * N) * c) _ hcof.2.2
    intro a b hab
    rcases hab with hab | hba
    · exact Or.inl (hscale a b hab)
    · exact Or.inr (hscale b a hba)
  have hstart : slot.a * N ∣ (p * N) * first := by
    rcases hfirstdvd with ⟨k, hk⟩
    refine ⟨p * k, ?_⟩
    rw [hk]
    ring
  have hfinish : slot.a' * N ∣ (p * N) * last := by
    rcases hlastdvd with ⟨k, hk⟩
    refine ⟨p * k, ?_⟩
    rw [hk]
    ring
  have hleftchain :
      ([slot.a * N] ++ (cofactors J r).map (fun c => (p * N) * c)).IsChain
        Comparable := by
    change (slot.a * N :: (cofactors J r).map (fun c => (p * N) * c)).IsChain _
    apply hscaledChain.cons
    intro y hy
    have hy' : (p * N) * first = y := by
      simpa [List.head?_map, hfirst] using hy
    subst y
    exact Or.inl hstart
  have hlastleft :
      ([slot.a * N] ++ (cofactors J r).map (fun c => (p * N) * c)).getLast? =
        some ((p * N) * last) := by
    rw [List.getLast?_append, List.getLast?_map, hlast]
    rfl
  have hframed :
      ([slot.a * N] ++ (cofactors J r).map (fun c => (p * N) * c) ++
        [slot.a' * N]).IsChain Comparable := by
    apply hleftchain.append (List.isChain_singleton (slot.a' * N))
    intro x hx y hy
    have hx' : (p * N) * last = x := by
      rw [hlastleft] at hx
      exact Option.mem_some_iff.mp hx
    have hy' : slot.a' * N = y := by simpa using hy
    subst x
    subst y
    exact Or.inr hfinish
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [framedBlock, scaledCofactors] using hframed
  · change ((cofactors J r).map (fun c => (p * N) * c)).Nodup
    apply List.Nodup.map _ hcof.2.1
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp hN) hab
  · intro t ht
    change t ∈ (cofactors J r).map (fun c => (p * N) * c) at ht
    rcases List.mem_map.mp ht with ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    have hcZ := hbound c hc
    rw [hs] at hcZ
    have hcle : c ≤ j / p := Int.ofNat_le.mp hcZ
    calc
      (p * N) * c = N * (p * c) := by ring
      _ ≤ N * (p * (j / p)) :=
        Nat.mul_le_mul_left N (Nat.mul_le_mul_left p hcle)
      _ ≤ N * j := Nat.mul_le_mul_left N (Nat.mul_div_le j p)
  · change ((cofactors J r).map (fun c => (p * N) * c)).length = _
    rw [List.length_map]
    exact hlen
  · have hJlen := Foundation.tablePath_length J hJ.1
    unfold gain
    omega

def DivisorGraphRuleH.LocalInsertion.results : Prop := True
