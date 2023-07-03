/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.MetricSpace.Baire

/-!
# Barrelled spaces
-/

open Bornology Set ContinuousLinearMap

class BarrelledSpace (𝕜 E : Type _) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p

instance {𝕜 E : Type _} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [BaireSpace E] :
    BarrelledSpace 𝕜 E where
  continuous_of_lowerSemicontinuous := by
    intro p hp
    have h₁ : ∀ n : ℕ, IsClosed (p.closedBall (0 : E) n) := fun n ↦ by
      simpa [p.closedBall_zero_eq] using hp.isClosed_preimage n
    have h₂ : (⋃ n : ℕ, p.closedBall (0 : E) n) = univ :=
      eq_univ_of_forall fun x ↦ mem_iUnion.mpr (exists_nat_ge <| p (x - 0))
    rcases nonempty_interior_of_iUnion_of_closed h₁ h₂ with ⟨n, ⟨x, hxn⟩⟩
    refine Seminorm.continuous' (show (0 : ℝ) < 2*n+1 by positivity) ?_
    rw [p.closedBall_zero_eq] at hxn ⊢
    have hxn' : p x ≤ n := by convert interior_subset hxn
    -- `hxn` says that `∀ᶠ y in 𝓝 0, p (x + y) ≤ n`.
    rw [mem_interior_iff_mem_nhds, ← map_add_left_nhds_zero] at hxn
    filter_upwards [hxn] with y hy
    calc p y = p (x + y - x) := by rw [add_sub_cancel']
      _ ≤ p (x + y) + p x := map_sub_le_add _ _ _
      _ ≤ n + n := add_le_add hy hxn'
      _ ≤ 2*n + 1 := by linarith

theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type _} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp

theorem Seminorm.continuous_iSup {ι 𝕜 E : Type _} [NormedField 𝕜]  [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i : Seminorm 𝕜 E) := by
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply

theorem WithSeminorms.banach_steinhaus {ι κ 𝕜₁ 𝕜₂ E F : Type _} [Nonempty κ]
    [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] [UniformSpace E]
    [UniformSpace F] [UniformAddGroup E] [UniformAddGroup F] [ContinuousSMul 𝕜₁ E]
    [ContinuousSMul 𝕜₂ F] [BarrelledSpace 𝕜₁ E]
    {q : SeminormFamily 𝕜₂ F κ} {𝓕 : ι → E →SL[σ₁₂] F}
    (hq : WithSeminorms q) (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup ((toLinearMap) ∘ 𝓕)).mpr ?_
  intro k
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩