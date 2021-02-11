import data_util.lean_step
import data_util.basic
import system.io
import all

meta def dummy_dp_handler : ℕ → ℕ → tactic.ref ℕ → ℕ → LeanStepDatapoint → tactic unit := λ _ _ _ _ dp, do {
  dp_fmt ← has_to_format.to_format <$> (to_tactic_json dp),
  tactic.trace format! "DATAPOINT: \n---\n{dp_fmt}\n---\n"
}

meta def fp_dp_handler
  (fp : io.handle)
  (serialization_guard : LeanStepDatapoint → tactic bool)
  (decl_count : ℕ)
  (decl_total : ℕ)
  (dp_count : tactic.ref ℕ)
  (total : ℕ)
  : LeanStepDatapoint → tactic unit := λ dp, do {
  mcond (bnot <$> serialization_guard dp) (pure ()) $ do {
    msg ← (format.to_string ∘ format.flatten ∘ has_to_format.to_format) <$> to_tactic_json dp,
    tactic.unsafe_run_io $ io.fs.put_str_ln fp msg
  },
  tactic.modify_ref dp_count nat.succ,
  count ← tactic.read_ref dp_count,
  when (count % 100 = 0) $ 
  tactic.trace format! "DECL {decl_count}/{decl_total} || PROCESSED {count}/{total}"
}

meta def lean_step_serialization_guard
  (SERIALIZATION_DEPTH_LIMIT := 64)
  (SERIALIZATION_WEIGHT_LIMIT := 1500)
  : LeanStepDatapoint → tactic bool := λ dp, do {
  let validate_expr : expr → bool := λ e, (e.get_depth ≤ SERIALIZATION_DEPTH_LIMIT) && (e.get_weight ≤ SERIALIZATION_WEIGHT_LIMIT),
  option.is_some <$> match dp with
  | ⟨_, decl_tp, hyps, _, decl_premises, _, goal, proof_term, result, next_lemma, _⟩ := optional $ do {
    guard $ validate_expr decl_tp,
    guard $ all $ hyps.map (λ ⟨x₁, x₂⟩, validate_expr x₁ && validate_expr x₂),
    guard $ all $ decl_premises.map (λ ⟨x₁, x₂⟩, validate_expr x₁ && validate_expr x₂),
    guard $ validate_expr proof_term,
    guard $ validate_expr result,
    match next_lemma with
    | (some next_lemma) := guard $ (validate_expr next_lemma.1) && (validate_expr next_lemma.2)
    | _ := pure ()
    end
  }
  end
}

meta def declaration.kind : declaration → string
| (declaration.defn _ _ _ _ _ _) := "definition"
| (declaration.thm _ _ _ _) := "theorem"
| (declaration.cnst _ _ _ _) := "constant"
| (declaration.ax _ _ _) := "axiom"

meta def lean_step_main
  (dp_handler : ℕ → ℕ → tactic.ref ℕ → ℕ → LeanStepDatapoint → tactic unit)
  (opts : LeanStepOpts)
  (decl_nm : name)
  (decl_count : ℕ) (decl_total : ℕ)
  : tactic unit := do {
  env ← tactic.get_env,
  decl ← env.get decl_nm | tactic.fail format! "[lean_step_main] DECLARATION LOOKUP FAILED FOR {decl_nm}",
  guard (decl.is_theorem) <|> tactic.fail format! "[lean_step_main] PROOF LOOKUP FAILED FOR {decl_nm}, DECLARATION IS A {decl.kind}",
  pf ← tactic.get_proof decl,
  decl_premises ← gather_used_premises pf >>= λ xs, xs.mmap mk_type_annotation,
  tactic.using_new_ref (0 : ℕ) $ λ dp_ref,
  lean_step_main_core decl_nm decl.type decl_premises pf (dp_handler decl_count decl_total dp_ref opts.rec_limit) opts pf
}

section tests

-- run_cmd lean_step_main dummy_dp_handler {} `peirce_identity 0 0

example : ∀ {P Q : Prop}, ((P → Q) → P) → P :=
λ {P Q : Prop}, (em P).elim (λ (_x : P) (_x_1 : (P → Q) → P), _x) $ λ (_x : ¬P) (H : (P → Q) → P), H (λ (_x_1 : P), (@absurd P false _x_1 _x).elim)

end tests

section main

meta def lean_step_from_decls_file (decls_file : string) (dest : string) (rec_limit : ℕ) (depth_limit : ℕ) (weight_limit : ℕ) : io unit := do {
  nm_strs ← io.mk_file_handle decls_file io.mode.read >>= readlines',
  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },
  let total := nms.length,
  dest_handle ← io.mk_file_handle dest io.mode.write,
  io.run_tactic' $ tactic.using_new_ref (0 : ℕ) $ λ ref,
  for_ nms $ λ ⟨nm, _⟩, do {
    count ← tactic.read_ref ref,
    tactic.try_verbose $ lean_step_main (fp_dp_handler dest_handle (lean_step_serialization_guard depth_limit weight_limit)) {rec_limit := rec_limit} nm count total,
    tactic.modify_ref ref nat.succ,
    count ← tactic.read_ref ref,
    tactic.trace format!"[lean_step_from_decls_file] PROGRESS: {count}/{total}"
  }
}

meta def list.nth_except_with_default {α} [has_to_format α] (xs : list α) (pos : ℕ) (msg : string) (default : option α := none) : io α :=
match default with
| some default := xs.nth_except pos msg <|> io.put_str_ln' format! "WARNING: defaulting {msg} to {default}" *> pure default
| _ := xs.nth_except pos msg
end

def nat.to_string : ℕ → string := repr

meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← args.nth_except 0 "decls_file",
  dest ← args.nth_except 1 "dest",
  rec_limit ← string.to_nat <$> args.nth_except_with_default 2 "rec_limit" (5000 : ℕ).to_string,
  serialization_depth_limit ← string.to_nat <$> (args.nth_except_with_default 3 "serialization_depth_limit" (100 : ℕ).to_string),
  serialization_weight_limit ← string.to_nat <$> (args.nth_except_with_default 4 "serialization_weight_limit" (2000 : ℕ).to_string),
  lean_step_from_decls_file decls_file dest rec_limit serialization_depth_limit serialization_weight_limit 
}

end main
