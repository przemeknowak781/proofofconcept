import TreeEntropy.APriori

/-!
# The dart system with a parameter: levels, monotonicity, the limit

For a multigraph `src tgt : E → V` and `z ∈ [0, 1]` the *dart system* is

    h_{u→v} · (d_u − z · Σ_{darts into u other than v→u} h) = z      for every dart u → v.

Its least nonnegative solution is built here as the limit of the levels

    level 0 = 0,     level (t+1)_{u→v} = z / (d_u − z · Σ_{darts into u other than v→u} level t).

No random walk and no universal cover is used: on the universal cover the level `t` would be the
generating function, at `z`, of the first visit to `v` within depth `t`, but that interpretation
is not needed.

Hypotheses on the graph (the class of the paper, without connectivity and looplessness, which
are not needed here): every degree is at least `2`, and no edge joins two vertices of degree `2`.

Results, for `0 ≤ z ≤ 1`:

* `good_lev`      : every level is nonnegative and satisfies the a priori bounds;
* `lev_le_succ`   : the levels increase with `t`;
* `lev_mono_z`    : the levels increase with `z`;
* `tendsto_levP`, `tendsto_levM` : they converge, to `solP`, `solM`;
* `sol_fix_p`, `sol_fix_m` : the limit solves the dart system;
* `sol_good`, `sol_mono_z`, `sol_pos`;
* `darts_sol_one` : at `z = 1` the limit satisfies all hypotheses of the edge inequality, hence
* `xi_one_le`     : `∑ v, log (d_v − inSum v) − ∑ e, log (1 − hp e · hm e) ≤ |E| · (1/2) log (27/8)`
                    for the solution at `z = 1`, with no further hypothesis.
-/

open Finset Filter Topology

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- The sum over the darts into `src e` other than the reverse of the dart `src e → tgt e`. -/
def othP (src tgt : E → V) (hp hm : E → ℝ) (e : E) : ℝ := inSum src tgt hp hm (src e) - hm e

/-- The sum over the darts into `tgt e` other than the reverse of the dart `tgt e → src e`. -/
def othM (src tgt : E → V) (hp hm : E → ℝ) (e : E) : ℝ := inSum src tgt hp hm (tgt e) - hp e

theorem othP_eq [DecidableEq E] (src tgt : E → V) (hp hm : E → ℝ) (e : E) :
    othP src tgt hp hm e = ∑ e' ∈ univ.filter (fun e' => tgt e' = src e), hp e'
      + ∑ e' ∈ (univ.filter (fun e' => src e' = src e)).erase e, hm e' := by
  have he : e ∈ univ.filter (fun e' => src e' = src e) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  unfold othP inSum
  rw [← Finset.add_sum_erase _ hm he]
  ring

theorem othM_eq [DecidableEq E] (src tgt : E → V) (hp hm : E → ℝ) (e : E) :
    othM src tgt hp hm e = ∑ e' ∈ (univ.filter (fun e' => tgt e' = tgt e)).erase e, hp e'
      + ∑ e' ∈ univ.filter (fun e' => src e' = tgt e), hm e' := by
  have he : e ∈ univ.filter (fun e' => tgt e' = tgt e) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  unfold othM inSum
  rw [← Finset.add_sum_erase _ hp he]
  ring

theorem othP_nonneg (src tgt : E → V) {hp hm : E → ℝ} (h1 : ∀ e, 0 ≤ hp e) (h2 : ∀ e, 0 ≤ hm e)
    (e : E) : 0 ≤ othP src tgt hp hm e := by
  classical
  rw [othP_eq]
  exact add_nonneg (Finset.sum_nonneg fun e' _ => h1 e') (Finset.sum_nonneg fun e' _ => h2 e')

theorem othM_nonneg (src tgt : E → V) {hp hm : E → ℝ} (h1 : ∀ e, 0 ≤ hp e) (h2 : ∀ e, 0 ≤ hm e)
    (e : E) : 0 ≤ othM src tgt hp hm e := by
  classical
  rw [othM_eq]
  exact add_nonneg (Finset.sum_nonneg fun e' _ => h1 e') (Finset.sum_nonneg fun e' _ => h2 e')

theorem othP_mono (src tgt : E → V) {hp hm hp' hm' : E → ℝ} (h1 : ∀ e, hp e ≤ hp' e)
    (h2 : ∀ e, hm e ≤ hm' e) (e : E) : othP src tgt hp hm e ≤ othP src tgt hp' hm' e := by
  classical
  rw [othP_eq, othP_eq]
  exact add_le_add (Finset.sum_le_sum fun e' _ => h1 e') (Finset.sum_le_sum fun e' _ => h2 e')

theorem othM_mono (src tgt : E → V) {hp hm hp' hm' : E → ℝ} (h1 : ∀ e, hp e ≤ hp' e)
    (h2 : ∀ e, hm e ≤ hm' e) (e : E) : othM src tgt hp hm e ≤ othM src tgt hp' hm' e := by
  classical
  rw [othM_eq, othM_eq]
  exact add_le_add (Finset.sum_le_sum fun e' _ => h1 e') (Finset.sum_le_sum fun e' _ => h2 e')

/-- One step of the iteration, for the dart `src e → tgt e`. -/
noncomputable def stepP (src tgt : E → V) (z : ℝ) (hp hm : E → ℝ) (e : E) : ℝ :=
  z / ((deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e)

/-- One step of the iteration, for the dart `tgt e → src e`. -/
noncomputable def stepM (src tgt : E → V) (z : ℝ) (hp hm : E → ℝ) (e : E) : ℝ :=
  z / ((deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e)

/-- The levels of the iteration. -/
noncomputable def lev (src tgt : E → V) (z : ℝ) : ℕ → (E → ℝ) × (E → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | t + 1 => (stepP src tgt z (lev src tgt z t).1 (lev src tgt z t).2,
      stepM src tgt z (lev src tgt z t).1 (lev src tgt z t).2)

/-- Nonnegative dart values that satisfy the a priori bounds. -/
def Good (src tgt : E → V) (hp hm : E → ℝ) : Prop :=
  (∀ e, 0 ≤ hp e) ∧ (∀ e, 0 ≤ hm e) ∧ Bounded src tgt hp hm

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg in
theorem Good.othP_le {hp hm : E → ℝ} (G : Good src tgt hp hm) (e : E) :
    othP src tgt hp hm e ≤ 3 / 4 * ((deg src tgt (src e) : ℝ) - 1) :=
  inSum_sub_hm_le src tgt hp hm e (3 / 4) (fun e' _ => G.2.2.hp_le hdeg e')
    (fun e' _ _ => G.2.2.hm_le hdeg e')

include hdeg in
theorem Good.othM_le {hp hm : E → ℝ} (G : Good src tgt hp hm) (e : E) :
    othM src tgt hp hm e ≤ 3 / 4 * ((deg src tgt (tgt e) : ℝ) - 1) :=
  inSum_sub_hp_le src tgt hp hm e (3 / 4) (fun e' _ _ => G.2.2.hp_le hdeg e')
    (fun e' _ => G.2.2.hm_le hdeg e')

include hdeg in
/-- The denominator of the step is at least `(d + 3)/4`. -/
theorem Good.denP {hp hm : E → ℝ} (G : Good src tgt hp hm) {z : ℝ} (hz1 : z ≤ 1)
    (e : E) : ((deg src tgt (src e) : ℝ) + 3) / 4
      ≤ (deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e := by
  have h1 := G.othP_le hdeg e
  have h0 := othP_nonneg src tgt G.1 G.2.1 e
  nlinarith [hz1, mul_nonneg (sub_nonneg.2 hz1) h0]

include hdeg in
theorem Good.denM {hp hm : E → ℝ} (G : Good src tgt hp hm) {z : ℝ} (hz1 : z ≤ 1)
    (e : E) : ((deg src tgt (tgt e) : ℝ) + 3) / 4
      ≤ (deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e := by
  have h1 := G.othM_le hdeg e
  have h0 := othM_nonneg src tgt G.1 G.2.1 e
  nlinarith [hz1, mul_nonneg (sub_nonneg.2 hz1) h0]

include hdeg in
theorem Good.denP_pos {hp hm : E → ℝ} (G : Good src tgt hp hm) {z : ℝ}
    (hz1 : z ≤ 1) (e : E) : 0 < (deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e := by
  have h := G.denP hdeg hz1 e
  have hd : (0:ℝ) ≤ deg src tgt (src e) := Nat.cast_nonneg _
  linarith

include hdeg in
theorem Good.denM_pos {hp hm : E → ℝ} (G : Good src tgt hp hm) {z : ℝ}
    (hz1 : z ≤ 1) (e : E) : 0 < (deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e := by
  have h := G.denM hdeg hz1 e
  have hd : (0:ℝ) ≤ deg src tgt (tgt e) := Nat.cast_nonneg _
  linarith

include hdeg hD in
/-- One step preserves `Good`. -/
theorem good_step {hp hm : E → ℝ} (G : Good src tgt hp hm) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Good src tgt (stepP src tgt z hp hm) (stepM src tgt z hp hm) := by
  have nn_p : ∀ e, 0 ≤ stepP src tgt z hp hm e := fun e =>
    div_nonneg hz0 (G.denP_pos hdeg hz1 e).le
  have nn_m : ∀ e, 0 ≤ stepM src tgt z hp hm e := fun e =>
    div_nonneg hz0 (G.denM_pos hdeg hz1 e).le
  refine ⟨nn_p, nn_m, bounded_step hdeg hD G.2.2 (fun e => ?_) (fun e => ?_)⟩
  · have hpos := G.denP_pos hdeg hz1 e
    have h0 := othP_nonneg src tgt G.1 G.2.1 e
    have hval : stepP src tgt z hp hm e
        * ((deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e) = z := by
      unfold stepP
      field_simp
    have hle : (deg src tgt (src e) : ℝ) - othP src tgt hp hm e
        ≤ (deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e := by nlinarith
    calc stepP src tgt z hp hm e
          * ((deg src tgt (src e) : ℝ) - (inSum src tgt hp hm (src e) - hm e))
        ≤ stepP src tgt z hp hm e
          * ((deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e) :=
          mul_le_mul_of_nonneg_left hle (nn_p e)
      _ = z := hval
      _ ≤ 1 := hz1
  · have hpos := G.denM_pos hdeg hz1 e
    have h0 := othM_nonneg src tgt G.1 G.2.1 e
    have hval : stepM src tgt z hp hm e
        * ((deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e) = z := by
      unfold stepM
      field_simp
    have hle : (deg src tgt (tgt e) : ℝ) - othM src tgt hp hm e
        ≤ (deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e := by nlinarith
    calc stepM src tgt z hp hm e
          * ((deg src tgt (tgt e) : ℝ) - (inSum src tgt hp hm (tgt e) - hp e))
        ≤ stepM src tgt z hp hm e
          * ((deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e) :=
          mul_le_mul_of_nonneg_left hle (nn_m e)
      _ = z := hval
      _ ≤ 1 := hz1

include hdeg hD in
/-- Every level is nonnegative and satisfies the a priori bounds. -/
theorem good_lev {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ t, Good src tgt (lev src tgt z t).1 (lev src tgt z t).2
  | 0 => ⟨fun _ => le_rfl, fun _ => le_rfl, bounded_zero src tgt⟩
  | t + 1 => good_step hdeg hD (good_lev hz0 hz1 t) hz0 hz1

include hdeg in
/-- The step is monotone in the dart values and in `z`. -/
theorem stepP_mono {hp hm hp' hm' : E → ℝ} (G' : Good src tgt hp' hm') {z z' : ℝ} (hz0 : 0 ≤ z)
    (hzz : z ≤ z') (hz1 : z' ≤ 1) (h0p : ∀ e, 0 ≤ hp e) (h0m : ∀ e, 0 ≤ hm e)
    (h1 : ∀ e, hp e ≤ hp' e) (h2 : ∀ e, hm e ≤ hm' e) (e : E) :
    stepP src tgt z hp hm e ≤ stepP src tgt z' hp' hm' e := by
  have hX := othP_mono src tgt h1 h2 e
  have hX0 := othP_nonneg src tgt h0p h0m e
  have hden' := G'.denP_pos hdeg hz1 e
  have hden : 0 < (deg src tgt (src e) : ℝ) - z * othP src tgt hp hm e := by
    have : z * othP src tgt hp hm e ≤ z' * othP src tgt hp' hm' e :=
      mul_le_mul hzz hX hX0 (hz0.trans hzz)
    linarith
  unfold stepP
  rw [div_le_div_iff₀ hden hden']
  have hd : (0:ℝ) ≤ deg src tgt (src e) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hz0 (hz0.trans hzz)) (sub_nonneg.2 hX),
    mul_nonneg (sub_nonneg.2 hzz) hd]

include hdeg in
theorem stepM_mono {hp hm hp' hm' : E → ℝ} (G' : Good src tgt hp' hm') {z z' : ℝ} (hz0 : 0 ≤ z)
    (hzz : z ≤ z') (hz1 : z' ≤ 1) (h0p : ∀ e, 0 ≤ hp e) (h0m : ∀ e, 0 ≤ hm e)
    (h1 : ∀ e, hp e ≤ hp' e) (h2 : ∀ e, hm e ≤ hm' e) (e : E) :
    stepM src tgt z hp hm e ≤ stepM src tgt z' hp' hm' e := by
  have hX := othM_mono src tgt h1 h2 e
  have hX0 := othM_nonneg src tgt h0p h0m e
  have hden' := G'.denM_pos hdeg hz1 e
  have hden : 0 < (deg src tgt (tgt e) : ℝ) - z * othM src tgt hp hm e := by
    have : z * othM src tgt hp hm e ≤ z' * othM src tgt hp' hm' e :=
      mul_le_mul hzz hX hX0 (hz0.trans hzz)
    linarith
  unfold stepM
  rw [div_le_div_iff₀ hden hden']
  have hd : (0:ℝ) ≤ deg src tgt (tgt e) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hz0 (hz0.trans hzz)) (sub_nonneg.2 hX),
    mul_nonneg (sub_nonneg.2 hzz) hd]

include hdeg hD in
/-- The levels increase with `z`. -/
theorem lev_mono_z {z z' : ℝ} (hz0 : 0 ≤ z) (hzz : z ≤ z') (hz1 : z' ≤ 1) :
    ∀ t, (∀ e, (lev src tgt z t).1 e ≤ (lev src tgt z' t).1 e) ∧
      (∀ e, (lev src tgt z t).2 e ≤ (lev src tgt z' t).2 e)
  | 0 => ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | t + 1 => by
      obtain ⟨ih1, ih2⟩ := lev_mono_z hz0 hzz hz1 t
      have G := good_lev hdeg hD hz0 (hzz.trans hz1) t
      have G' := good_lev hdeg hD (hz0.trans hzz) hz1 t
      exact ⟨fun e => stepP_mono hdeg G' hz0 hzz hz1 G.1 G.2.1 ih1 ih2 e,
        fun e => stepM_mono hdeg G' hz0 hzz hz1 G.1 G.2.1 ih1 ih2 e⟩

include hdeg hD in
/-- The levels increase with `t`. -/
theorem lev_le_succ {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ t, (∀ e, (lev src tgt z t).1 e ≤ (lev src tgt z (t + 1)).1 e) ∧
      (∀ e, (lev src tgt z t).2 e ≤ (lev src tgt z (t + 1)).2 e)
  | 0 => ⟨fun e => (good_lev hdeg hD hz0 hz1 1).1 e, fun e => (good_lev hdeg hD hz0 hz1 1).2.1 e⟩
  | t + 1 => by
      obtain ⟨ih1, ih2⟩ := lev_le_succ hz0 hz1 t
      have G := good_lev hdeg hD hz0 hz1 t
      have G' := good_lev hdeg hD hz0 hz1 (t + 1)
      exact ⟨fun e => stepP_mono hdeg G' hz0 le_rfl hz1 G.1 G.2.1 ih1 ih2 e,
        fun e => stepM_mono hdeg G' hz0 le_rfl hz1 G.1 G.2.1 ih1 ih2 e⟩

/-- The limit of the levels, dart `src e → tgt e`. -/
noncomputable def solP (src tgt : E → V) (z : ℝ) (e : E) : ℝ := ⨆ t, (lev src tgt z t).1 e

/-- The limit of the levels, dart `tgt e → src e`. -/
noncomputable def solM (src tgt : E → V) (z : ℝ) (e : E) : ℝ := ⨆ t, (lev src tgt z t).2 e

include hdeg hD in
theorem tendsto_levP {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (e : E) :
    Tendsto (fun t => (lev src tgt z t).1 e) atTop (𝓝 (solP src tgt z e)) := by
  apply tendsto_atTop_ciSup
  · exact monotone_nat_of_le_succ fun t => (lev_le_succ hdeg hD hz0 hz1 t).1 e
  · exact ⟨3 / 4, by
      rintro _ ⟨t, rfl⟩
      exact (good_lev hdeg hD hz0 hz1 t).2.2.hp_le hdeg e⟩

include hdeg hD in
theorem tendsto_levM {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (e : E) :
    Tendsto (fun t => (lev src tgt z t).2 e) atTop (𝓝 (solM src tgt z e)) := by
  apply tendsto_atTop_ciSup
  · exact monotone_nat_of_le_succ fun t => (lev_le_succ hdeg hD hz0 hz1 t).2 e
  · exact ⟨3 / 4, by
      rintro _ ⟨t, rfl⟩
      exact (good_lev hdeg hD hz0 hz1 t).2.2.hm_le hdeg e⟩

include hdeg hD in
/-- The limit is nonnegative and satisfies the a priori bounds. -/
theorem sol_good {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Good src tgt (solP src tgt z) (solM src tgt z) :=
  ⟨fun e => ge_of_tendsto' (tendsto_levP hdeg hD hz0 hz1 e)
      fun t => (good_lev hdeg hD hz0 hz1 t).1 e,
    fun e => ge_of_tendsto' (tendsto_levM hdeg hD hz0 hz1 e)
      fun t => (good_lev hdeg hD hz0 hz1 t).2.1 e,
    bounded_of_tendsto (fun t => (good_lev hdeg hD hz0 hz1 t).2.2)
      (tendsto_levP hdeg hD hz0 hz1) (tendsto_levM hdeg hD hz0 hz1)⟩

include hdeg hD in
/-- Every level is below the limit. -/
theorem lev_le_sol {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (t : ℕ) :
    (∀ e, (lev src tgt z t).1 e ≤ solP src tgt z e) ∧
      (∀ e, (lev src tgt z t).2 e ≤ solM src tgt z e) :=
  ⟨fun e => (monotone_nat_of_le_succ fun t => (lev_le_succ hdeg hD hz0 hz1 t).1 e).ge_of_tendsto
      (tendsto_levP hdeg hD hz0 hz1 e) t,
    fun e => (monotone_nat_of_le_succ fun t => (lev_le_succ hdeg hD hz0 hz1 t).2 e).ge_of_tendsto
      (tendsto_levM hdeg hD hz0 hz1 e) t⟩

include hdeg hD in
/-- The limit increases with `z`. -/
theorem sol_mono_z {z z' : ℝ} (hz0 : 0 ≤ z) (hzz : z ≤ z') (hz1 : z' ≤ 1) :
    (∀ e, solP src tgt z e ≤ solP src tgt z' e) ∧ (∀ e, solM src tgt z e ≤ solM src tgt z' e) :=
  ⟨fun e => le_of_tendsto_of_tendsto' (tendsto_levP hdeg hD hz0 (hzz.trans hz1) e)
      (tendsto_levP hdeg hD (hz0.trans hzz) hz1 e) fun t => (lev_mono_z hdeg hD hz0 hzz hz1 t).1 e,
    fun e => le_of_tendsto_of_tendsto' (tendsto_levM hdeg hD hz0 (hzz.trans hz1) e)
      (tendsto_levM hdeg hD (hz0.trans hzz) hz1 e) fun t => (lev_mono_z hdeg hD hz0 hzz hz1 t).2 e⟩

omit [DecidableEq V] in
theorem tendsto_inSum [DecidableEq V] {Hp Hm : ℕ → E → ℝ} {hp hm : E → ℝ}
    (limp : ∀ e, Tendsto (fun t => Hp t e) atTop (𝓝 (hp e)))
    (limm : ∀ e, Tendsto (fun t => Hm t e) atTop (𝓝 (hm e))) (v : V) :
    Tendsto (fun t => inSum src tgt (Hp t) (Hm t) v) atTop (𝓝 (inSum src tgt hp hm v)) := by
  unfold inSum
  exact (tendsto_finsetSum _ fun e _ => limp e).add (tendsto_finsetSum _ fun e _ => limm e)

include hdeg hD in
/-- **The limit solves the dart system** (dart `src e → tgt e`). -/
theorem sol_fix_p {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (e : E) :
    solP src tgt z e * ((deg src tgt (src e) : ℝ)
      - z * othP src tgt (solP src tgt z) (solM src tgt z) e) = z := by
  have limp := tendsto_levP hdeg hD hz0 hz1
  have limm := tendsto_levM hdeg hD hz0 hz1
  have h1 : Tendsto (fun t => (lev src tgt z (t + 1)).1 e) atTop (𝓝 (solP src tgt z e)) :=
    (tendsto_add_atTop_iff_nat 1).2 (limp e)
  have h2 : Tendsto (fun t => (deg src tgt (src e) : ℝ)
      - z * othP src tgt (lev src tgt z t).1 (lev src tgt z t).2 e) atTop
      (𝓝 ((deg src tgt (src e) : ℝ) - z * othP src tgt (solP src tgt z) (solM src tgt z) e)) := by
    unfold othP
    exact tendsto_const_nhds.sub (((tendsto_inSum limp limm (src e)).sub (limm e)).const_mul z)
  have h3 := h1.mul h2
  have h4 : ∀ t, (lev src tgt z (t + 1)).1 e * ((deg src tgt (src e) : ℝ)
      - z * othP src tgt (lev src tgt z t).1 (lev src tgt z t).2 e) = z := by
    intro t
    have hpos := (good_lev hdeg hD hz0 hz1 t).denP_pos hdeg hz1 e
    show stepP src tgt z (lev src tgt z t).1 (lev src tgt z t).2 e * _ = z
    unfold stepP
    field_simp
  exact tendsto_nhds_unique h3 (by simp only [h4]; exact tendsto_const_nhds)

include hdeg hD in
/-- **The limit solves the dart system** (dart `tgt e → src e`). -/
theorem sol_fix_m {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (e : E) :
    solM src tgt z e * ((deg src tgt (tgt e) : ℝ)
      - z * othM src tgt (solP src tgt z) (solM src tgt z) e) = z := by
  have limp := tendsto_levP hdeg hD hz0 hz1
  have limm := tendsto_levM hdeg hD hz0 hz1
  have h1 : Tendsto (fun t => (lev src tgt z (t + 1)).2 e) atTop (𝓝 (solM src tgt z e)) :=
    (tendsto_add_atTop_iff_nat 1).2 (limm e)
  have h2 : Tendsto (fun t => (deg src tgt (tgt e) : ℝ)
      - z * othM src tgt (lev src tgt z t).1 (lev src tgt z t).2 e) atTop
      (𝓝 ((deg src tgt (tgt e) : ℝ) - z * othM src tgt (solP src tgt z) (solM src tgt z) e)) := by
    unfold othM
    exact tendsto_const_nhds.sub (((tendsto_inSum limp limm (tgt e)).sub (limp e)).const_mul z)
  have h3 := h1.mul h2
  have h4 : ∀ t, (lev src tgt z (t + 1)).2 e * ((deg src tgt (tgt e) : ℝ)
      - z * othM src tgt (lev src tgt z t).1 (lev src tgt z t).2 e) = z := by
    intro t
    have hpos := (good_lev hdeg hD hz0 hz1 t).denM_pos hdeg hz1 e
    show stepM src tgt z (lev src tgt z t).1 (lev src tgt z t).2 e * _ = z
    unfold stepM
    field_simp
  exact tendsto_nhds_unique h3 (by simp only [h4]; exact tendsto_const_nhds)

include hdeg hD in
/-- For `z > 0` the solution is positive. -/
theorem sol_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (∀ e, 0 < solP src tgt z e) ∧ (∀ e, 0 < solM src tgt z e) := by
  have G := sol_good hdeg hD hz0.le hz1
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rcases (G.1 e).eq_or_lt with h | h
    · have := sol_fix_p hdeg hD hz0.le hz1 e
      rw [← h, zero_mul] at this
      linarith
    · exact h
  · rcases (G.2.1 e).eq_or_lt with h | h
    · have := sol_fix_m hdeg hD hz0.le hz1 e
      rw [← h, zero_mul] at this
      linarith
    · exact h

include hdeg hD in
/-- At `z = 1` the limit satisfies every hypothesis of the edge inequality. -/
theorem darts_sol_one : Darts src tgt (solP src tgt 1) (solM src tgt 1) := by
  have G := sol_good hdeg hD zero_le_one le_rfl
  have hpos := sol_pos hdeg hD zero_lt_one le_rfl
  refine ⟨hpos.1, hpos.2, fun e => ?_, fun e => ?_, hdeg, hD, G.2.2.1, G.2.2.2.1, G.2.2.2.2.1,
    G.2.2.2.2.2⟩
  · have h := sol_fix_p hdeg hD zero_le_one le_rfl e
    unfold othP at h
    calc _ = _ := by ring
      _ = 1 := h
  · have h := sol_fix_m hdeg hD zero_le_one le_rfl e
    unfold othM at h
    calc _ = _ := by ring
      _ = 1 := h

include hdeg hD in
/-- **The edge inequality for the solution at `z = 1`**, with no hypothesis beyond the two
conditions on the degrees. -/
theorem xi_one_le [Fintype V] :
    ∑ v, Real.log ((deg src tgt v : ℝ) - inSum src tgt (solP src tgt 1) (solM src tgt 1) v)
        - ∑ e, Real.log (1 - solP src tgt 1 e * solM src tgt 1 e)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) :=
  tree_entropy_bound_of_darts' (darts_sol_one hdeg hD)

end ClassC

end Kenyon
