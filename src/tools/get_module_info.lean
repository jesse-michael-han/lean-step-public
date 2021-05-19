import ..data_util.util
import all

section main
open tactic

meta def list.drop_until {α} [decidable_eq α] : list α → (α → bool) → list α
| arg@(x::xs) y := if (bnot $ y x) then list.drop_until xs y else arg
| [] _ := []

meta def get_top_level_module_name (decl_nm : name) : tactic string := do {
  env ← tactic.get_env,
  xs ← (string.split (λ c, c = '/')) <$> env.decl_olean decl_nm,
  (xs.drop_until $ (λ x, x = "src" ∨ x = "library")).nth 1
}

meta def main : io unit := do {
  args ← io.cmdline_args,

  (some decls_file) ← (pure $ args.nth 0) | io.fail' format!"MUST SUPPLY decls_file AS FIRST ARGUMENT",
  (some dest) ← (pure $ args.nth 1) | io.fail' format!"MUST SUPPLY dest AS SECOND ARGUMENT",


  nm_strs ← (io.mk_file_handle decls_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),
  
  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },

  f ← io.mk_file_handle dest io.mode.write,
  for_ nms $ λ ⟨nm, _⟩, do {
    m_nm ← io.run_tactic' $ (get_top_level_module_name nm) <|> pure "none",
    io.fs.put_str_ln f $ format.to_string $ format!"{nm} {m_nm}",
    io.put_str_ln' format!"PROCESSED DECL: {nm}"
  }
}

end main
