theory Repaired_Sheaf
  imports "Grothendieck_Schemes_Repaired.Scheme"
begin

text \<open>In the repaired entry, covers are indexed by sets of subsets of the space. The
repaired predicate \<open>sheaf_of_rings\<close> then implies locality and gluing for families indexed
by a set of an arbitrary type, which is the usual sheaf condition.\<close>

lemma (in sheaf_of_rings) glueing_arbitrary_index:
  fixes I :: "'i set" and V :: "'i \<Rightarrow> 'a set" and s :: "'i \<Rightarrow> 'b"
  assumes U: "is_open U"
    and V: "\<And>i. i \<in> I \<Longrightarrow> is_open (V i) \<and> V i \<subseteq> U \<and> s i \<in> \<FF> (V i)"
    and cov: "U \<subseteq> (\<Union>i\<in>I. V i)"
    and compat: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow>
      \<rho> (V i) (V i \<inter> V j) (s i) = \<rho> (V j) (V i \<inter> V j) (s j)"
  shows "\<exists>t. t \<in> \<FF> U \<and> (\<forall>i\<in>I. \<rho> U (V i) t = s i)"
proof -
  define pick where "pick W = (SOME i. i \<in> I \<and> V i = W)" for W
  define s' where "s' W = s (pick W)" for W
  have pick: "pick W \<in> I \<and> V (pick W) = W" if "W \<in> V ` I" for W
  proof -
    have "\<exists>i. i \<in> I \<and> V i = W" using that by auto
    then show ?thesis unfolding pick_def by (rule someI_ex)
  qed
  have key: "s' (V i) = s i" if "i \<in> I" for i
  proof -
    let ?j = "pick (V i)"
    have j: "?j \<in> I" "V ?j = V i" using pick[of "V i"] that by auto
    have "\<rho> (V i) (V i) (s i) = \<rho> (V i) (V i) (s ?j)"
      using compat[OF that j(1)] j(2) by simp
    then show ?thesis using V[OF that] V[OF j(1)] j(2) by (simp add: s'_def)
  qed
  have oc: "open_cover_of_open_subset S is_open U (V ` I) (\<lambda>W. W)"
  proof
    show "U \<subseteq> S" using U by (rule open_imp_subset)
    show "W \<subseteq> S" if "W \<in> V ` I" for W using that V open_imp_subset by auto
    show "U \<subseteq> (\<Union>W\<in>V ` I. W)" using cov by auto
    show "is_open W" if "W \<in> V ` I" for W using that V by auto
    show "is_open U" by (rule U)
  qed
  have "\<exists>t. t \<in> \<FF> U \<and> (\<forall>W. W \<in> V ` I \<longrightarrow> \<rho> U W t = s' W)"
  proof (rule glueing[OF oc])
    show "\<forall>W. W \<in> V ` I \<longrightarrow> W \<subseteq> U \<and> s' W \<in> \<FF> W" using V key by auto
    show "\<rho> W (W \<inter> W') (s' W) = \<rho> W' (W \<inter> W') (s' W')" if "W \<in> V ` I" "W' \<in> V ` I" for W W'
      using that compat key by auto
  qed
  then show ?thesis using key by auto
qed

lemma (in sheaf_of_rings) locality_arbitrary_index:
  fixes I :: "'i set" and V :: "'i \<Rightarrow> 'a set"
  assumes U: "is_open U"
    and V: "\<And>i. i \<in> I \<Longrightarrow> is_open (V i) \<and> V i \<subseteq> U"
    and cov: "U \<subseteq> (\<Union>i\<in>I. V i)"
    and s: "s \<in> \<FF> U"
    and zero: "\<And>i. i \<in> I \<Longrightarrow> \<rho> U (V i) s = \<zero>\<^bsub>V i\<^esub>"
  shows "s = \<zero>\<^bsub>U\<^esub>"
proof -
  have oc: "open_cover_of_open_subset S is_open U (V ` I) (\<lambda>W. W)"
  proof
    show "U \<subseteq> S" using U by (rule open_imp_subset)
    show "W \<subseteq> S" if "W \<in> V ` I" for W using that V open_imp_subset by auto
    show "U \<subseteq> (\<Union>W\<in>V ` I. W)" using cov by auto
    show "is_open W" if "W \<in> V ` I" for W using that V by auto
    show "is_open U" by (rule U)
  qed
  show ?thesis
    using locality[OF oc _ s] V zero by auto
qed

ML \<open>
  val _ =
    if null (Thm_Deps.all_oracles [@{thm sheaf_of_rings.glueing_arbitrary_index},
      @{thm sheaf_of_rings.locality_arbitrary_index}]) then ()
    else error "A repaired-predicate result depends on an oracle";
\<close>

end
