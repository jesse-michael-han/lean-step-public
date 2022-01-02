import ..data_util.util
import all

section main
open tactic

meta def main : io unit := do {
  args ← io.cmdline_args,
  let dest : string := ((args.nth 0).get_or_else "./data/mathlib_decls.log"),
  let ignore_decls_fn : environment → declaration → bool :=
    (λ e d, declaration.is_auto_or_internal e d || bnot (declaration.is_theorem d) || d.to_name.is_aux),
  f ← io.mk_file_handle dest io.mode.append,
  io.run_tactic' $ do {
    env ← get_env,
    mathlib_dir ← get_mathlib_dir,
    decls ← list.filter (λ d, !(ignore_decls_fn env d)) <$> (lint_project_decls mathlib_dir),
    for_ decls $ λ decl, do {
      let decl_name := decl.to_name.to_string,
      tactic.unsafe_run_io $ io.fs.put_str_ln f decl_name,
      tactic.trace format!"DECL: {decl_name}"
    }
  }
}

end main
