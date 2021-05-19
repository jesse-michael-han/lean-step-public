-- import all
-- import utils.util
-- import data_util.basic
-- import data_util.lean_step
-- import lean_step

-- -- #check times_cont_diff_at_of_subsingleto

-- #check continuous_linear_map.complete_space

-- #check abs_max_sub_max_le_abs


-- theorem triangle_inequality {α} [_inst_1 : normed_group α]
--   (g h : α) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
-- begin
--   convert dist_triangle g 0 (-h); rw [dist_eq_norm],
--     { rw [sub_neg_eq_add] },
--     { rw [sub_zero] },
--     { rw [sub_neg_eq_add, zero_add] }
-- end


-- run_cmd do {
--   pf ← tactic.get_proof_from_env `norm_add_le >>= expr.unfold_macros,
--   tactic.pp pf >>= tactic.trace
-- }

-- run_cmd do {
--   pf ← tactic.get_proof_from_env `triangle_inequality >>= expr.unfold_macros,
--   tactic.pp pf >>= tactic.trace
-- }
-- -- #check lean_step_main
-- -- run_cmd lean_step_main dummy_dp_handler {rec_limit := 1000} `triangle_inequality 0 0
-- theorem iff_of_true' {P} : (P ↔ true) → P :=
-- begin
--   intro H, cases H with H₁ H₂, apply H₂, trivial
-- end
-- #check iff_of_true'
