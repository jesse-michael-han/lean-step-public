import .util

section tactic
open tactic
open interaction_monad.result
meta def tactic.try_verbose {α} (tac : tactic α) : tactic unit := λ s, match tac s with
| (exception msg pos state) := match msg with
  | (some thunk) := (tactic.trace format! "[try_verbose] FAILURE: {thunk ()}") s
  | none := success () s
  end
| (success _ s') := success () s'
end

end tactic

section mfold_with_binders

namespace expr

-- this should satisfy the following invariants:
-- the variable binding list should only inherit from higher binders, so there is a tree of local bindings
-- the accumulator α, however, should be folded across the entire tree
meta def expr.mfold_with_binders_aux {α : Type} : expr → α → (list expr) → (expr → α → (list expr) → tactic α) → (tactic α)
| e@(var k) acc bs f := f e acc bs
| e@(sort l) acc bs f := f e acc bs
| e@(const nm ls) acc bs f := f e acc bs
| e@(mvar _ _ _) acc bs f := f e acc bs
| e@(local_const _ _ _ _) acc bs f := f e acc bs
| e@(app e₁ e₂) acc bs f := do {
    r₀ ← f e acc bs,
    r₁ ← expr.mfold_with_binders_aux e₁ r₀ bs f,
    r₂ ← expr.mfold_with_binders_aux e₂ r₁ bs f,
    pure r₂
  }
| e@(lam var_name b_info var_type body) acc bs f := do {
    ⟨[b], e'⟩ ← tactic.open_n_lambdas e 1,
    r ← expr.mfold_with_binders_aux e' acc (b::bs) f,
    pure r
  }
| e@(pi var_name b_info var_type body) acc bs f := do {
    ⟨[b], e'⟩ ← tactic.open_n_pis e 1,
    r ← expr.mfold_with_binders_aux e' acc (b::bs) f,
    pure r
  }
| e@(elet var_name var_type var_assignment body) acc bs f := do {
    expr.mfold_with_binders_aux e.reduce_let acc bs f
  }
| e@(macro _ _) acc bs f := do {
  (e.unfold_macros) >>= (λ x, f x acc bs)
}

meta def mfold_with_binders {α : Type} : expr → α → (expr → α → (list expr) → tactic α) → tactic α :=
λ e acc f, expr.mfold_with_binders_aux e acc [] f

end expr

end mfold_with_binders

section generic

-- TODO(): probably buggy! don't trust io.fs.get_line
meta def readlines (f : io.handle) : io (list string) := do {
  ls ← io.iterate [] (λ acc, do {
     do {
      r ← buffer.to_string <$> io.fs.get_line f,
      mcond (io.fs.is_eof f) (pure none) $ do
      -- io.put_str_ln $ "GOT STRING: " ++ r,
      pure ∘ pure $ acc ++ [r]
    }
  }),
  pure ls
}

-- note(): use this instead
meta def readlines' (f : io.handle) : io (list string) := do {
  list.filter (λ x, !(x = "")) <$> (string.split (= '\n') <$> buffer.to_string <$> io.fs.read_to_end f)
}

meta def dump_step
  {datapoint_type : Type}
  {worker_fn_options_type : Type}
  (r : tactic.ref ℕ)
  (decl : declaration)
  (dest_handle : io.handle)
  (serialization_guard : datapoint_type → tactic bool)
  (worker_fn : expr → worker_fn_options_type → tactic (list datapoint_type))
  (serialization_fn : datapoint_type → tactic string)
  (worker_fn_options : worker_fn_options_type)
  (desc : string)
: tactic unit :=
do {
  tactic.trace format!"[dump_{desc}_step] PROCESSING DECL {decl.to_name}",
  pf ← tactic.get_proof decl,
  dps ← worker_fn pf worker_fn_options,
  for_ dps $ λ dp, do {
    mcond (bnot <$> serialization_guard dp) (pure ()) $ do
    msg ← serialization_fn dp,
    tactic.unsafe_run_io $ io.fs.put_str_ln dest_handle msg
  },
  tactic.modify_ref r nat.succ
}

/- TODO(): it is inefficient to eagerly produce an entire list of datapoints first before serialization.
  In practice, this seems to work OK, but we might hit performance problems when we try to do everything at once
  might be better to make `serialization_fn` an argument to `worker_fn` and have it write datapoints to the file
  in a loop. -/
meta def dump_from_decls_file
  /- `datapoint_type` and `worker_fn_options_type` should be inferred automatically from `worker_fn` -/
  {datapoint_type : Type}
  {worker_fn_options_type : Type}

  /- used to populate stdout trace message -/
  (desc : string)
  /- file containing a list of Lean declarations -/
  (decls_file : string)
  /- destination filepath for the serialized datapoints -/
  (dest : string)
  /- returns tt if OK to serialize-/
  (serialization_guard : datapoint_type → tactic bool)
  /- responsible for extracting a list of datapoints from the declaration -/
  (worker_fn : expr → worker_fn_options_type → tactic (list datapoint_type))
  /- responsible for writing the datapoint_type to a string, which is then written to the file -/
  (serialization_fn : datapoint_type → tactic string)
  /- configuration (e.g. recursion limits) for the worker_fn, which is responsible for extracting datapoints -/
  (worker_fn_options : worker_fn_options_type)

: io unit := do {
  nm_strs ← io.mk_file_handle decls_file io.mode.read >>= readlines',
  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },
  dest_handle ← io.mk_file_handle dest io.mode.write,
  io.run_tactic $ do {
    env ← tactic.get_env,
    let total := nms.length,
    tactic.trace format!"TOTAL: {total}",
    tactic.using_new_ref (0 : ℕ) $ λ r,
    for_ nms $ λ ⟨nm, _⟩, do {
      decl ← optional (env.get nm),
      match decl with
      | (some decl) := do {
          dump_step r decl dest_handle serialization_guard worker_fn serialization_fn worker_fn_options desc
        }
      | none := do {
        tactic.trace format!"[WARNING] COULDN'T RESOLVE {nm}",
        tactic.modify_ref r nat.succ
      }
      end,
      count ← tactic.read_ref r,
      tactic.trace format!"PROGRESS: {count}/{total}"
    }
  }
}

end generic

section premise_selection

meta def gather_used_premises : expr → tactic (list expr) := λ e,
  let fn : expr → list expr → list expr → tactic (list expr) := λ e acc bs, do {
    match e with
      | ex@(expr.const nm levels) := mcond (tactic.is_proof ex) (pure $ ex::acc) (pure acc)
      | _ := pure acc
    end
  } in
  e.mfold_with_binders [] fn

meta def mk_type_annotation : expr → tactic (expr × expr) :=
λ h, prod.mk h <$> tactic.infer_type h

end premise_selection

section pp

meta def enable_verbose : tactic unit := do {
-- tactic.set_bool_option `pp.implicit true
  tactic.set_bool_option `pp.all true,
  tactic.set_bool_option `pp.implicit true, -- TODO(): can we get away with setting this `false`? this blows up the proof terms by a LOT
  tactic.set_bool_option `pp.universes false,
  tactic.set_bool_option `pp.notation true,
  tactic.set_bool_option `pp.generalized_field_notation true,
  tactic.set_bool_option `pp.structure_projections true,
  tactic.set_bool_option `pp.beta true,
  tactic.set_bool_option `pp.binder_types true,
  tactic.set_nat_option `pp.max_depth 128,
  tactic.set_nat_option `pp.max_steps 10000
}

meta def with_verbose {α} (tac : tactic α) : tactic α :=
tactic.save_options $ enable_verbose *> tac

end pp

section test_lemmas
  -- GOAL P Q : Prop ⊢ ((P → Q) → P) → P PROOFSTEP apply or.elim (em P)
  -- GOAL P Q : Prop ⊢ P → ((P → Q) → P) → P  P Q : Prop ⊢ ¬P → ((P → Q) → P) → P PROOFSTEP intros h _
  -- GOAL P Q : Prop, h : P, ᾰ : (P → Q) → P ⊢ P  P Q : Prop ⊢ ¬P → ((P → Q) → P) → P PROOFSTEP exact h
  -- GOAL P Q : Prop ⊢ ¬P → ((P → Q) → P) → P PROOFSTEP tauto!
lemma peirce_identity {P Q :Prop} : ((P → Q) → P) → P :=
begin
  apply or.elim (em P),
  intros h _,
  exact h,
  tauto!
end

end test_lemmas
