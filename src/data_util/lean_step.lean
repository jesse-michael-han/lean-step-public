import data_util.basic

section LeanStep



@[derive has_to_format]
meta structure LeanStepDatapoint : Type :=
(decl_nm : name)
(decl_tp : expr)
(hyps : list (expr × expr))
(hyps_mask : list bool) -- TODO(): convert hyps_mask and decl_premises_mask into name_sets?
(decl_premises : list (expr × expr)) -- this is computed once and for all before beginning the recursion
(decl_premises_mask : list bool)
(goal : expr)
(proof_term : expr)
(result : expr) -- global proof term with metavariable in place of the subterm at point, for skip-tree tasks; can be computed using `expr.replace`; optionally, use meta.expr.lens and track this along with the binders
(next_lemma : option (expr × expr))
(goal_is_prop : bool)

notation `to_tactic_json` := has_to_tactic_json.to_tactic_json

/- TODO(): optionally use `with_verbose` -/
meta instance : has_to_tactic_json expr :=
⟨λ e, (json.of_string ∘ format.to_string ∘ format.flatten) <$> tactic.pp e⟩

meta instance has_to_tactic_json_of_has_coe_json {α} [has_coe α json] : has_to_tactic_json α :=
⟨λ x, pure ↑x⟩

meta instance has_to_tactic_json_list {α} [has_to_tactic_json α] : has_to_tactic_json (list α) :=
let fn : list α → tactic json := λ xs, json.array <$> (xs.mmap to_tactic_json) in
⟨fn⟩

meta instance has_to_tactic_json_prod {α β} [has_to_tactic_json α] [has_to_tactic_json β] : has_to_tactic_json (α × β) :=
let fn : α × β → tactic json := λ ⟨a,b⟩,
json.array <$> ((::) <$> to_tactic_json a <*> pure <$> to_tactic_json b)
in ⟨fn⟩

meta def name.to_json' : name → json := λ nm, json.of_string nm.to_string

meta instance has_to_tactic_json_option {α} [has_to_tactic_json α] : has_to_tactic_json (option α) :=
let fn : option α → tactic json := λ x,
  match x with
  | (some val) := to_tactic_json val
  | none := pure $ json.null
  end in ⟨fn⟩

meta instance : has_to_tactic_json LeanStepDatapoint :=
let fn : LeanStepDatapoint → tactic json := λ x, do {
  tactic.set_nat_option `pp.max_depth 128,
  tactic.set_nat_option `pp.max_steps 10000,
  match x with
  | ⟨decl_nm, decl_tp, hyps, hyps_mask,
     decl_premises, decl_premises_mask,
     goal, proof_term, result, next_lemma, goal_is_prop⟩ := do {
    json.object <$> do {
      decl_tp_json ← to_tactic_json decl_tp,
      hyps_json ← to_tactic_json hyps,
      hyps_mask_json ← to_tactic_json hyps_mask,
      decl_premises_json ← to_tactic_json decl_premises,
      decl_premises_mask_json ←  to_tactic_json decl_premises_mask,
      goal_json ← to_tactic_json goal,
      proof_term_json ← to_tactic_json proof_term,
      result_json ←  to_tactic_json result,
      verbose_goal_json ← with_verbose $ to_tactic_json goal,
      verbose_result_json ← with_verbose $ to_tactic_json result,
      verbose_proof_term_json ← with_verbose $ to_tactic_json proof_term,
      next_lemma_json ← to_tactic_json next_lemma,
      pure $
        [
            ("decl_nm", decl_nm.to_json')
          , ("decl_tp", decl_tp_json)
          , ("hyps", hyps_json)
          , ("hyps_mask", hyps_mask_json)
          , ("decl_premises", decl_premises_json)
          , ("decl_premises_mask", decl_premises_mask_json)
          , ("goal", goal_json)
          , ("proof_term", proof_term_json)
          , ("result", result_json)
          , ("next_lemma", next_lemma_json)
          , ("goal_is_prop", goal_is_prop)
          , ("verbose_proof_term", verbose_proof_term_json)
          , ("verbose_goal", verbose_goal_json)
          , ("verbose_result", verbose_result_json)
        ]
    }
  }
  end
}
in ⟨fn⟩

def PREDICT : true := trivial

-- TODO(): test
-- TODO(): even if this works as intended, it will produce unwanted behavior when trying to replace
-- local constants, due to variable shadowing, and basically can't be used except for constants
meta def expr.replace_with_predict (pf : expr) (subterm : expr) : tactic expr := do
  c ← tactic.mk_const `PREDICT,
  pure $ pf.replace (λ e _, if e.hash = subterm.hash then pure c else none)
section replace_at
open expr

meta def expr.replace_at : expr → expr.address → expr → tactic expr
| e@(var k) addr e' := match addr with
  | [] := pure e'
  | _ := pure e
  end
| e@(sort l) addr e' := match addr with
  | [] := pure e'
  | _ := pure e
  end
| e@(mvar _ _ _) addr e' := pure e
| e@(const nm _) addr e' := match addr with
  | [] := pure e'
  | _ := pure e
  end
| e@(local_const unique pp bi type) addr e' := match addr with
  | [] := pure e'
  | exc := pure e
  end
| e@(app e₁ e₂) addr e' := match addr with
  | [] := pure e'
  | (expr.coord.app_fn::xs) := do {
  new_hd ← expr.replace_at e₁ xs e',
  pure $ app new_hd e₂
}
  | (expr.coord.app_arg::xs) := app e₁ <$> expr.replace_at e₂ xs e'
  | _ := pure e
  end
| e@(lam var_name b_info var_type body) addr e' := match addr with
  | [] := pure e'
  | (expr.coord.lam_body::xs) := do {
  ⟨[b], new_body⟩ ← tactic.open_n_lambdas e 1,
    flip expr.bind_lambda b <$> (expr.replace_at new_body xs e')
  }
  | _ := pure e
  end
| e@(pi var_name b_info var_type body) addr e' := match addr with
  | [] := pure e'
  | (expr.coord.pi_body::xs) := do {
  ⟨[b], new_body⟩ ← tactic.open_n_pis e 1,
    flip expr.bind_pi b <$> (expr.replace_at new_body xs e')
  }
  | _ := pure e
  end
| e@(elet var_name var_type var_assignment body) addr e' := expr.replace_at e.reduce_let addr e'
| e@(expr.macro _ _) addr e' := e.unfold_macros >>= λ x, expr.replace_at x addr e'

end replace_at

meta def expr.replace_with_predict_at (pf : expr) (addr : expr.address) : tactic expr := do {
  c ← tactic.mk_const `PREDICT,
  pf.replace_at addr c
}

meta structure LeanStepState : Type :=
(count : ℕ := 0)

meta structure LeanStepOpts : Type :=
(rec_limit := 5000)

open expr

meta def extract_next_lemma : expr → tactic (expr × expr)
| e@(app e₁ e₂) := do {
  let hd := (get_app_fn e),
  prod.mk hd <$> tactic.infer_type hd
}
| e@(const _ _) := do {
  prod.mk e <$> tactic.infer_type e
}
| e@(local_const _ _ _ _) := do {
  prod.mk e <$> tactic.infer_type e
}
| _ := tactic.fail "[extract_next_lemma] not an application"


section 
open native
meta def rb_set.union {α} : rb_set α → rb_set α → rb_set α :=
λ s₁ s₂, rb_set.fold s₁ s₂ $ flip rb_set.insert
end 

local notation `LEAN_STEP_TRACE` := ff

meta def lean_step_trace (fmt : format) : tactic unit := do {
  when LEAN_STEP_TRACE $ tactic.trace fmt
}

meta def lean_step_main_core_aux 
  (decl_nm : name) 
  (decl_tp : expr) 
  (decl_premises : list (expr × expr)) 
  (main_pf : expr) 
  (dp_handler : LeanStepDatapoint → tactic unit) : Π 
  (acc : LeanStepState) 
  (opts : LeanStepOpts) 
  (bs : list (expr × expr)) 
  (addr : expr.address) /- always the current address of `pf` wrt `main_pf` -/
  (pf : expr), tactic (expr_set × name_set × LeanStepState) := λ acc opts bs addr pf,
(guard (acc.count ≤ opts.rec_limit) <|> tactic.fail format! "[lean_step_main_core_aux] RECURSION LIMIT HIT: {acc.count}") *>
match acc, opts, bs, addr, pf with
| acc, opts, bs, addr, e@(var k) := do lean_step_trace "[lean_step_main_core_aux] VAR CASE",
  pure $ ⟨mk_expr_set, mk_name_set, {count := acc.count + 1}⟩
| acc, opts, bs, addr, e@(sort _) := do lean_step_trace "[lean_step_main_core_aux] SORT CASE",
  pure $ ⟨mk_expr_set, mk_name_set, {count := acc.count + 1}⟩
| acc, opts, bs, addr, e@(mvar _ _ _) := do lean_step_trace "[lean_step_main_core_aux] MVAR CASE",
  pure $ ⟨mk_expr_set, mk_name_set, {count := acc.count + 1}⟩
| acc, opts, bs, addr, e@(const nm ls) := do lean_step_trace "[lean_step_main_core_aux] CONST CASE", do {
  (dp : LeanStepDatapoint) ← do {
    goal ← tactic.infer_type e,
    goal_is_prop ← tactic.is_prop goal,
    result ← main_pf.replace_with_predict e,
    next_lemma ← optional $ extract_next_lemma e,
    pure $ ({
        decl_nm := decl_nm
      , decl_tp := decl_tp
      , hyps := bs
      , hyps_mask := list.repeat ff bs.length
      , decl_premises := decl_premises
      , decl_premises_mask := decl_premises.map (λ c, c.1.const_name = nm)
      , goal := goal
      , proof_term := e
      , result := result
      , next_lemma := next_lemma
      , goal_is_prop := goal_is_prop
    } : LeanStepDatapoint)
  },

  -- when true $ sorry, -- write the datapoint
  dp_handler dp,
  -- tactic.fail "NYI"
  pure ⟨mk_expr_set, mk_name_set.insert nm, {count := acc.count + 1}⟩
}
| acc, opts, bs, addr, e@(local_const unique pretty bi tp) := do lean_step_trace "[lean_step_main_core_aux] LOCAL CONST CASE", do {
  (dp : LeanStepDatapoint) ← do {
    goal ← tactic.infer_type e,
    goal_is_prop ← tactic.is_prop goal,
    result ← main_pf.replace_with_predict_at addr,
    next_lemma ← optional $ extract_next_lemma e,
    pure $ ({
        decl_nm := decl_nm
      , decl_tp := decl_tp
      , hyps := bs
      , hyps_mask := bs.map (λ c, to_bool $ c.1 = e)
      , decl_premises := decl_premises
      , decl_premises_mask := list.repeat ff decl_premises.length
      , goal := goal
      , proof_term := e
      , result := result
      , next_lemma := next_lemma
      , goal_is_prop := goal_is_prop
    } : LeanStepDatapoint)
  },
  dp_handler dp,
  pure ⟨mk_expr_set.insert e, mk_name_set, {count := acc.count + 1}⟩
}
| acc, opts, bs, addr, e@(app e₁ e₂) := do lean_step_trace "[lean_step_main_core_aux] APP CASE", do {
    ⟨lc_set₁, c_set₁, acc⟩ ← lean_step_main_core_aux acc opts bs (addr ++ [expr.coord.app_fn]) e₁,
    (lc_set₂, c_set₂, acc) ← lean_step_main_core_aux acc opts bs (addr ++ [expr.coord.app_arg]) e₂,
    let lc_set : expr_set := lc_set₁.union lc_set₂,
    let hyps_mask := bs.map (λ c, lc_set.contains c.1),
    let c_set : name_set := c_set₁.union c_set₂,
    let decl_premises_mask := decl_premises.map (λ c, c_set.contains c.1.const_name),
  (dp : LeanStepDatapoint) ← do {
    goal ← tactic.infer_type e,
    goal_is_prop ← tactic.is_prop goal,
    result ← main_pf.replace_with_predict_at addr,
    next_lemma ← optional $ extract_next_lemma e,
    pure $ ({
        decl_nm := decl_nm
      , decl_tp := decl_tp
      , hyps := bs
      , hyps_mask := hyps_mask
      , decl_premises := decl_premises
      , decl_premises_mask := decl_premises_mask
      , goal := goal
      , proof_term := e
      , result := result
      , next_lemma := next_lemma
      , goal_is_prop := goal_is_prop
    } : LeanStepDatapoint)
  },
  dp_handler dp,
  pure ⟨lc_set, c_set, {count := acc.count + 1}⟩
}
| acc, opts, bs, addr, e@(lam var_name b_info var_type body) := do lean_step_trace "[lean_step_main_core_aux] LAM CASE", do {
  ⟨[b], new_body⟩ ← tactic.open_n_lambdas e 1,
  -- new_bs ← mcond (tactic.is_proof b) (pure $ b::bs) (pure bs),
  
  new_bs ← (++) bs <$> pure <$> mk_type_annotation b,

  ⟨lc_set, c_set, acc⟩ ← lean_step_main_core_aux acc opts new_bs (addr ++ [coord.lam_body]) new_body,
  (dp : LeanStepDatapoint) ← do {
    goal ← tactic.infer_type e,
    goal_is_prop ← tactic.is_prop goal,
    result ← main_pf.replace_with_predict_at addr,
    next_lemma ← optional $ extract_next_lemma e,
    pure $ ({
        decl_nm := decl_nm
      , decl_tp := decl_tp
      , hyps := bs
      , hyps_mask := bs.map (λ x, lc_set.contains x.1)
      , decl_premises := decl_premises
      , decl_premises_mask := decl_premises.map (λ c, c_set.contains c.1.const_name)
      , goal := goal
      , proof_term := e
      , result := result
      , next_lemma := next_lemma
      , goal_is_prop := goal_is_prop
    } : LeanStepDatapoint)
  },
  dp_handler dp,
  pure ⟨lc_set, c_set, {count := acc.count + 1}⟩
}
-- TODO(): make this case a no-op?
| acc, opts, bs, addr, e@(pi var_name b_info var_type body) := do lean_step_trace "[lean_step_main_core_aux] PI CASE", do {
  ⟨[b], new_body⟩ ← tactic.open_n_pis e 1,
  -- new_bs ← mcond (tactic.is_proof b) (pure $ b::bs) (pure bs),
  
  new_bs ← (++) bs <$> pure <$> mk_type_annotation b,

  ⟨lc_set, c_set, acc⟩ ← lean_step_main_core_aux acc opts new_bs (addr ++ [coord.pi_body]) new_body,
  (dp : LeanStepDatapoint) ← do {
    goal ← tactic.infer_type e,
    goal_is_prop ← tactic.is_prop goal,
    result ← main_pf.replace_with_predict_at addr,
    next_lemma ← optional $ extract_next_lemma e,
    pure $ ({
        decl_nm := decl_nm
      , decl_tp := decl_tp
      , hyps := bs
      , hyps_mask := bs.map (λ x, lc_set.contains x.1)
      , decl_premises := decl_premises
      , decl_premises_mask := decl_premises.map (λ c, c_set.contains c.1.const_name)
      , goal := goal
      , proof_term := e
      , result := result
      , next_lemma := next_lemma
      , goal_is_prop := goal_is_prop
    } : LeanStepDatapoint)
  },
  dp_handler dp,
  pure ⟨lc_set, c_set, {count := acc.count + 1}⟩
}
| acc, opts, bs, addr, e@(elet var_name var_type var_assignment body) := do lean_step_trace "[lean_step_main_core_aux] LET CASE", do {
  lean_step_main_core_aux acc opts bs addr e.reduce_let -- should be fine as long as the expr.replace function has the same logic
}
-- TODO(): make no-op/throw exception?
| acc, opts, bs, addr, e@(macro _ _) := do lean_step_trace "[lean_step_main_core_aux] MACRO CASE", do {
  (e.unfold_macros) >>= (lean_step_main_core_aux acc opts bs addr)
}
end

meta def lean_step_main_core
(decl_nm : name)
(decl_tp : expr)
(decl_premises : list (expr × expr))
(main_pf : expr)
(dp_handler : LeanStepDatapoint → tactic unit)
(opts : LeanStepOpts)
: Π (pf : expr), tactic unit := λ pf, do {
 tactic.try_verbose $ (lean_step_main_core_aux decl_nm decl_tp decl_premises pf dp_handler {} opts [] [] pf) *> pure ()
}

end LeanStep
