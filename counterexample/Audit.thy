theory Audit
  imports Counterexample Stalk_Counterexample Scheme_Counterexample NC_Scheme
begin

text \<open>The build fails if any headline result depends on an oracle, which includes skipped
proofs. If the environment variable \<open>SCHEMES_AUDIT_FILE\<close> is set, the checked statements
are also written to that file.\<close>

ML \<open>
  val audit_thms =
   [("exists_stalkwise_iso_not_iso", @{thm exists_stalkwise_iso_not_iso}),
    ("exists_scheme_with_noncommutative_global_sections",
      @{thm exists_scheme_with_noncommutative_global_sections}),
    ("counterexample_to_arbitrary_gluing", @{thm counterexample_to_arbitrary_gluing}),
    ("sections_comm_ring", @{thm sections_comm_ring}),
    ("stalkwise_iso_not_iso", @{thm stalkwise_iso_not_iso}),
    ("stalkwise_iso_not_iso_ringed_spaces", @{thm stalkwise_iso_not_iso_ringed_spaces}),
    ("sheaf_of_rings.open_points_scheme", @{thm sheaf_of_rings.open_points_scheme}),
    ("sheaf_of_rings.open_points_scheme_field", @{thm sheaf_of_rings.open_points_scheme_field}),
    ("afp_scheme_without_gluing", @{thm afp_scheme_without_gluing}),
    ("afp_sheaf_with_noncommutative_global_sections",
      @{thm afp_sheaf_with_noncommutative_global_sections}),
    ("afp_scheme_with_noncommutative_global_sections",
      @{thm afp_scheme_with_noncommutative_global_sections})];
  val _ =
    if null (Thm_Deps.all_oracles (map snd audit_thms)) then ()
    else error "A headline result depends on an oracle";
  val _ =
    (case OS.Process.getEnv "SCHEMES_AUDIT_FILE" of
      NONE => ()
    | SOME "" => ()
    | SOME file =>
        let
          val ctxt = @{context};
          fun plain s = XML.content_of (YXML.parse_body s);
          fun show (name, th) =
            name ^ ":\n" ^ plain (Pretty.string_of (Thm.pretty_thm ctxt th)) ^ "\n\n";
        in
          File.write (Path.explode file)
            ("SCHEMES_AUDIT: no oracles or skipped proofs in the following results\n\n" ^
              implode (map show audit_thms))
        end);
\<close>

end
