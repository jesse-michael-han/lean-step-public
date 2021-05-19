import tactic
import control.traversable.derive
import data.string.basic
import meta.rb_map


infix `<e>`:100 := λ x y, tactic.to_expr y >>= x


section iterate_until

meta def iterate_until_aux
  {m} [monad m] [alternative m] {α}
  (tac :  m α) (stop : α → m bool) (fuel_exhausted_callback : m α)
  : Π (fuel : ℕ), m α
| 0 := do {result ← tac, mcond (stop result) (pure result) fuel_exhausted_callback}
| (n+1) := do { result ← tac, mcond (stop result) (pure result) (iterate_until_aux n)}

meta def iterate_until
  {m} [monad m] [alternative m] {α}
  (tac : m α) (stop : α → m bool) (fuel := 100000)
  (fuel_exhausted_callback : m α := alternative.failure)
  : m α
  :=
iterate_until_aux tac stop fuel_exhausted_callback fuel

end iterate_until


section

setup_tactic_parser

meta def parse_decl_nm_and_open_ns : string → tactic (name × list name) := λ inp,
flip lean.parser.run_with_input inp $ prod.mk <$> iterate_until ident (λ nm, pure ∘ bnot $ nm = name.anonymous) 100 <*> many ident

-- -- brilliant
-- #eval (["foo bar baz\n", "baz baz baz\n", "a b c d e\n"].mmap $ io.run_tactic' ∘ parse_decl_nm_and_open_ns) >>= λ x, io.put_str_ln' format!"{x}"

end


section io
open interaction_monad interaction_monad.result
namespace io

meta def run_tactic' {α} (tac :tactic α) : io α := do {
  io.run_tactic $ do {
    result ← tactic.capture tac,
    match result with
    | (success val _) := pure val
    | (exception m_fmt pos _) := do {
      let fmt_msg := (m_fmt.get_or_else (λ _, format!"none")) (),
      let msg := format!"[io.run_tactic'] {pos}: tactic failed\n-------\n{fmt_msg}\n-------\n",
      tactic.trace msg,
      tactic.fail msg
    }
    end
  }
}

end io
end io


section name

namespace name

meta def is_aux : name → bool
| name.anonymous := ff
| (name.mk_string str nm) := (||) ((list.head str.to_list) = '_') (is_aux nm)
| (name.mk_numeral _ nm) := is_aux nm

end name

end name


section util

namespace io

meta def fail' {α} (fmt : format) : io α := io.fail $ format.to_string fmt

meta def put_str_ln' : Π (fmt : format), io unit := io.put_str_ln ∘ format.to_string

namespace fs

def put_str_ln_flush (h : handle) (s : string) : io unit :=
put_str h s *> put_str h "\n" *> flush h

end fs

end io


section list_nth_except

-- convenience function for command-line argument parsing
meta def list.nth_except {α} : list α → ℕ → string → io α := λ xs pos msg,
  match (xs.nth pos) with
  | (some result) := pure result
  | none := do {
    io.fail' format!"must supply {msg} as argument {pos}"
  }
  end

end list_nth_except


def for_ {m α β} [monad m] (xs : list α) (body : α → m β) := list.mmap' body xs

def any : list bool -> bool := λ xs, xs.foldl (||) ff

def all : list bool → bool := λ xs, xs.foldl (&&) tt

inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat


namespace tactic

meta def guard_sorry : expr → tactic unit := λ e, do {
  contains_sorry_flag ← e.mfold ff (λ e' _ acc, if acc then pure acc else pure $ bor acc $ e'.is_sorry.is_some),
  guard $ bnot contains_sorry_flag
}

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

meta def get_proof : Π (decl : declaration), tactic expr
| (declaration.thm _ _ _ value_thunk) := pure $ value_thunk.get
| _ := tactic.fail ""

meta def test_get_proof (nm : name) : tactic unit := do {
  e <- tactic.get_env,
  d <- e.get nm,
  get_proof d >>= tactic.trace
}

meta def get_proof_from_env (nm : name) : tactic expr := do {
  e ← get_env,
  d ← e.get nm,
  get_proof d
}

/-- Prints a 'Try this:' message. -/
meta def trythis : string → tactic unit
| s := tactic.trace (sformat!"Try this: {s}")

end tactic

end util


section unfold_macros

meta def expr.unfold_string_macros {elab} : expr elab → expr elab
| e := match e.is_string_macro with
       | (some a) := expr.unfold_string_macros a
       | none := e
       end

meta def expr.unfold_macros (e : expr) : tactic expr := do {
  -- env ← tactic.get_env,
  -- pure $ env.unfold_all_macros e
  pure $ e.unfold_string_macros.erase_annotations
}

end unfold_macros


section derive_has_to_format

meta def expr.join (tp : expr) : list expr → tactic expr := λ xs,
xs.foldr (λ e₁ acc, do {acc ← acc, tactic.to_expr ``(@list.cons %%tp %%e₁ %%acc)}) (tactic.to_expr ``(list.nil))

meta def format.join_using : format → list format → format := λ x xs,
format.join $ list.intercalate [x] (pure <$> xs)

meta def format.apply_constructor : format → list format → format := λ f fs,
match fs with
| [] := f
| fs := format.join_using " " [f, format.join ["(", format.join_using " " fs, ")"]]
end

open tactic
namespace tactic
namespace interactive

meta def mk_to_format (type : name) : tactic unit := do {
  ls ← local_context,
  (x::_) ← tactic.intro_lst [`arg],
  et ← infer_type x,
  xs ← tactic.induction x,
  xs.mmap' $ λ ⟨c, args, _⟩, do
    (args', rec_call) ← args.mpartition $ λ e, do {
      e' ← tactic.to_expr ``(format),
      bnot <$> e'.occurs <$> tactic.infer_type e
    },
    args'' ← args'.mmap (λ a, flip prod.mk a <$> (et.occurs <$> tactic.infer_type a)),
    let fn : list (bool × expr) → state_t (list expr) tactic (list expr) := λ args'', do {
      let pop : state_t (list expr) tactic (option expr) := do {
        xs ← get,
        match xs with
        | (a::as) := modify (λ _, as) *> pure (some a)
        | [] := pure none
        end
      },
      args''.mmap (λ ⟨b, a⟩, if b then do (some x) ← pop, pure x else state_t.lift $ do
      a_tp ← infer_type a,
      _inst ← mk_app ``has_to_format [a_tp] >>= mk_instance,
      tactic.to_expr ``(@has_to_format.to_format _ (%%_inst) %%a))
    },
    args''' ← prod.fst <$> (fn args'').run rec_call,
    c ← tactic.resolve_constant c,
    nm_tp ← to_expr ``(name),
    nm_fmt ← mk_app ``has_to_format [nm_tp] >>= mk_instance,
    fs ← expr.join `(format) args''',
    result ← to_expr ``(format.apply_constructor (@has_to_format.to_format %%nm_tp %%nm_fmt %%c) %%fs),
    tactic.exact result
}

meta def derive_has_to_format (pre : option name) : tactic unit := do {
  vs ← local_context,
  `(has_to_format %%f) ← target,
  env ← get_env,
  let n := f.get_app_fn.const_name,
  d ← get_decl n,
  refine ``( { to_format := _ } ),
  tgt ← target,
  extract_def (with_prefix pre n <.> "to_format") ff $ mk_to_format n
}

meta def has_to_format_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``has_to_format (derive_has_to_format nspace) [] nspace

@[derive_handler]
meta def has_to_format_derive_handler : derive_handler :=
guard_class ``has_to_format has_to_format_derive_handler'

attribute [derive [has_to_format]] my_nat

end interactive
end tactic

end derive_has_to_format


section json

section has_to_json
universe u

meta class has_to_json (α : Type u) : Type (u+1) :=
(to_json : α → json)

meta class has_to_tactic_json (α : Type u) : Type (u+1) :=
(to_tactic_json : α → tactic json)

meta class has_from_json (α : Type u) : Type (u+1) :=
(from_json : json → tactic α)

end has_to_json

meta def list.lookup_prod {α β} : (list (α × β)) → (α → bool) → option β
| [] _ := none
| (⟨a,b⟩::xs) p := if p a then pure b else xs.lookup_prod p

meta def json.get_string : json → option string
| (json.of_string str) := pure str
| _ := none

meta def json.get_float : json → option native.float
| (json.of_float str) := pure str
| _ := none

meta def json.lookup : json → string → option json
| (json.object kvs) str := kvs.lookup_prod $ λ k, k = str
| _ _ := none

end json