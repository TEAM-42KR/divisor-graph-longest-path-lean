import Mathlib
import RuleHRelease.Definitions.Offers
set_option autoImplicit false

def DivisorGraphRuleH.Directories.results : Prop := True

theorem DivisorGraphRuleH.Directories.mem_pathPool (D : DivisorGraphRuleH.PoolDirectory) (s : ℤ) (J : List ℕ) :
    J ∈ DivisorGraphRuleH.pathPool D s ↔
      ∃ E ∈ D.entries, E.eligible ∧ E.grid ≤ D.scale ∧ (E.grid : ℤ) ≤ s ∧ E.path = J := by
  classical
  simp [DivisorGraphRuleH.pathPool, and_assoc]

theorem DivisorGraphRuleH.Directories.tablePathAt_of_mem (D : DivisorGraphRuleH.PoolDirectory)
    (hD : DivisorGraphRuleH.PoolHypotheses D) (s : ℤ)
    (J : List ℕ) (hJ : J ∈ DivisorGraphRuleH.pathPool D s) :
    DivisorGraphRuleH.TablePathAt J s := by
  obtain ⟨E, hE, he, hcut, hEs, rfl⟩ :=
    (DivisorGraphRuleH.Directories.mem_pathPool D s J).mp hJ
  obtain ⟨hpath, hbound⟩ := hD.2.1 E hE he hcut
  refine ⟨hpath, ?_⟩
  intro c hc
  have hcE : (c : ℤ) ≤ (E.grid : ℤ) := by
    exact_mod_cast hbound c hc
  exact hcE.trans hEs

theorem DivisorGraphRuleH.Directories.pathPool_nonempty (D : DivisorGraphRuleH.PoolDirectory)
    (hD : DivisorGraphRuleH.PoolHypotheses D) (s : ℤ) (hs : 6 ≤ s) :
    DivisorGraphRuleH.pathPool D s ≠ [] := by
  obtain ⟨E, hE, hmaster, hsix⟩ := hD.2.2
  have he : E.eligible := Or.inl hmaster
  have hcut : E.grid ≤ D.scale :=
    hsix.trans ((by decide : (6 : ℕ) ≤ 3000).trans hD.1)
  have hEsix : (E.grid : ℤ) ≤ 6 := by exact_mod_cast hsix
  have hmem : E.path ∈ DivisorGraphRuleH.pathPool D s :=
    (DivisorGraphRuleH.Directories.mem_pathPool D s E.path).mpr
      ⟨E, hE, he, hcut, hEsix.trans hs, rfl⟩
  exact List.ne_nil_of_mem hmem

theorem DivisorGraphRuleH.H5_directory (D : DivisorGraphRuleH.PoolDirectory) (hD : DivisorGraphRuleH.PoolHypotheses D)
    (s : ℤ) (hs : 6 ≤ s ∧ s ≤ (D.scale : ℤ))
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    DivisorGraphRuleH.pathPool D s ≠ [] ∧
    ∃ block : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.offer (DivisorGraphRuleH.pathPool D s) s slot = some block := by
  have hnonempty : DivisorGraphRuleH.pathPool D s ≠ [] :=
    DivisorGraphRuleH.Directories.pathPool_nonempty D hD s hs.1
  exact ⟨hnonempty, DivisorGraphRuleH.H5 (DivisorGraphRuleH.pathPool D s) s
    hnonempty (DivisorGraphRuleH.Directories.tablePathAt_of_mem D hD s) slot hslot hsize⟩
