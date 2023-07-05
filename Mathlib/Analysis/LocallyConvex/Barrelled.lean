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

open Filter Topology Set ContinuousLinearMap

section defs

/-- A topological vector space `E` is said to be "barrelled" if all lower semicontinuous seminorms
on `E` are actually continuous. This is not the usual definition for TVS over `ℝ` or `ℂ`, but this
has the big advantage of working and giving sensible results over *any* `NontriviallyNormedField`.
In particular, the Banach-Steinhaus theorem holds for maps between such a space and any space whose
topology is generated by a family of seminorms. -/
class BarrelledSpace (𝕜 E : Type _) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p

theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type _} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp

theorem Seminorm.continuous_iSup {ι 𝕜 E : Type _} [NormedField 𝕜]  [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i) := by
  rw [← Seminorm.coe_iSup_eq bdd]
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply

end defs

section TVS_anyField

variable {α ι κ 𝕜₁ 𝕜₂ E F : Type _} [Nonempty κ] [NontriviallyNormedField 𝕜₁]
    [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F]

/-- Any TVS over a `NontriviallyNormedField` that is also a Baire space is barrelled. In
particular, this applies to Banach spaces and Fréchet spaces. -/
instance [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜₁ E] [BaireSpace E] :
    BarrelledSpace 𝕜₁ E where
  continuous_of_lowerSemicontinuous := by
    -- Let `p` be a lower-semicontinuous seminorm on `E`.
    intro p hp
    -- Consider the family of all `p`-closed-balls with integer radius.
    -- By lower semicontinuity, each of these closed balls is indeed closed...
    have h₁ : ∀ n : ℕ, IsClosed (p.closedBall (0 : E) n) := fun n ↦ by
      simpa [p.closedBall_zero_eq] using hp.isClosed_preimage n
    -- ... and clearly they cover the whole space.
    have h₂ : (⋃ n : ℕ, p.closedBall (0 : E) n) = univ :=
      eq_univ_of_forall fun x ↦ mem_iUnion.mpr (exists_nat_ge <| p (x - 0))
    -- Hence, one of them has nonempty interior. Let `n : ℕ` be its radius, and fix `x` an
    -- interior point.
    rcases nonempty_interior_of_iUnion_of_closed h₁ h₂ with ⟨n, ⟨x, hxn⟩⟩
    -- To show that `p` is continuous, we will show that the `p`-closed-ball of
    -- radius `2*n` is a neighborhood of zero.
    refine Seminorm.continuous' (r := 2*n) ?_
    rw [p.closedBall_zero_eq] at hxn ⊢
    have hxn' : p x ≤ n := by convert interior_subset hxn
    -- By definition, we have `p x' ≤ n` for `x'` sufficiently close to `x`.
    -- In other words, `p (x + y) ≤ n` for `y` sufficiently close to `0`.
    rw [mem_interior_iff_mem_nhds, ← map_add_left_nhds_zero] at hxn
    -- Hence, for `y` sufficiently close to `0`, we have
    -- `p y = p(x + y - x) ≤ p (x + y) + p x ≤ 2*n`
    filter_upwards [hxn] with y hy
    calc p y = p (x + y - x) := by rw [add_sub_cancel']
      _ ≤ p (x + y) + p x := map_sub_le_add _ _ _
      _ ≤ n + n := add_le_add hy hxn'
      _ = 2*n := by ring

namespace WithSeminorms

variable [UniformSpace E] [UniformSpace F] [UniformAddGroup E] [UniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)

/-- The **Banach-Steinhaus** theorem for maps from a barrelled space to any space whose topology is
generated by a family of seminorms. Use `WithSeminorms.equicontinuous_TFAE` and
`Seminorm.bound_of_continuous` to get explicit bounds on the seminorms from equicontinuity. -/
protected theorem banach_steinhaus (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  -- We just have to prove that `⊔ i, (q k) ∘ (𝓕 i)` is a (well-defined) continuous seminorm
  -- for all `k`.
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup ((toLinearMap) ∘ 𝓕)).mpr ?_
  intro k
  -- By assumption the supremum `⊔ i, (q k) ∘ (𝓕 i)` is well-defined at each point, hence this
  -- is indeed a seminorm
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  -- And since it is a supremum of continuous seminorms and `E` is barrelled, it is continuous
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩

/-- Given a sequence of continuous linear maps which converges pointwise and for which the
domain is barrelled, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well.

This actually works for any *countably generated* filter instead of `AtTop : Filter ℕ`,
but the proof ultimately goes back to sequences. -/
protected def continuousLinearMapOfTendsto [T2Space F] {l : Filter α} [l.IsCountablyGenerated]
    [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F} (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F where
  toFun := f
  map_add' := (linearMapOfTendsto _ _ h).map_add'
  map_smul' := (linearMapOfTendsto _ _ h).map_smul'
  cont := by
    rcases l.exists_seq_tendsto with ⟨u, hu⟩
    refine (h.comp hu).continuous_of_equicontinuous_at (hq.banach_steinhaus ?_).equicontinuous
    intro k x
    rw [tendsto_pi_nhds] at h
    exact (((hq.continuous_seminorm k).tendsto _).comp <| (h x).comp hu).bddAbove_range
end WithSeminorms

end TVS_anyField
