theory Point_Schemes
  imports "Grothendieck_Schemes.Scheme"
begin

text \<open>General lemmas about the AFP locales: an open point whose ring of sections is a
commutative local ring with a single prime ideal is an affine chart, and a sheaf of rings
(in the AFP sense) on a space all of whose points are such is a scheme (in the AFP sense).
Nothing here depends on any particular presheaf.\<close>

section \<open>Generic helpers\<close>

lemma ring_homomorphismI:
  assumes "Ring_Theory.ring A addA multA zeroA oneA" "Ring_Theory.ring B addB multB zeroB oneB"
    and "f \<in> A \<rightarrow>\<^sub>E B"
    and "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> f (addA a b) = addB (f a) (f b)"
    and "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> f (multA a b) = multB (f a) (f b)"
    and "f zeroA = zeroB" "f oneA = oneB"
  shows "ring_homomorphism f A addA multA zeroA oneA B addB multB zeroB oneB"
proof -
  interpret src: Ring_Theory.ring A addA multA zeroA oneA by fact
  interpret tgt: Ring_Theory.ring B addB multB zeroB oneB by fact
  have hm: "Set_Theory.map f A B" using assms(3) by (simp add: Set_Theory.map_def)
  show ?thesis
    using hm src.ring_axioms tgt.ring_axioms
      src.additive.group_axioms tgt.additive.group_axioms
      src.additive.monoid_axioms tgt.additive.monoid_axioms
      src.multiplicative.monoid_axioms tgt.multiplicative.monoid_axioms assms(4-7)
    unfolding Ring_Theory.ring_homomorphism_def Group_Theory.group_homomorphism_def
      Group_Theory.monoid_homomorphism_def Group_Theory.monoid_homomorphism_axioms_def
    by blast
qed

lemma ring_isomorphismI:
  assumes "Ring_Theory.ring A addA multA zeroA oneA" "Ring_Theory.ring B addB multB zeroB oneB"
    and "f \<in> A \<rightarrow>\<^sub>E B"
    and "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> f (addA a b) = addB (f a) (f b)"
    and "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> f (multA a b) = multB (f a) (f b)"
    and "f zeroA = zeroB" "f oneA = oneB"
    and "bij_betw f A B"
  shows "ring_isomorphism f A addA multA zeroA oneA B addB multB zeroB oneB"
proof -
  have "ring_homomorphism f A addA multA zeroA oneA B addB multB zeroB oneB"
    by (rule ring_homomorphismI[OF assms(1-7)])
  moreover have "Set_Theory.map f A B" using assms(3) by (simp add: Set_Theory.map_def)
  ultimately show ?thesis
    using assms(8) by (simp add: ring_isomorphism_def bijective_map_def bijective_def)
qed

lemma trivial_ring_hom:
  assumes A: "ring A addA multA zeroA oneA" and B: "ring B addB multB zeroB oneB"
    and Bc: "B = {c}"
  shows "ring_homomorphism (\<lambda>s\<in>A. c) A addA multA zeroA oneA B addB multB zeroB oneB"
proof (rule ring_homomorphismI[OF A B])
  interpret A: ring A addA multA zeroA oneA by fact
  interpret B: ring B addB multB zeroB oneB by fact
  have c: "addB c c = c" "multB c c = c" "zeroB = c" "oneB = c"
    using B.additive.composition_closed[of c c] B.multiplicative.composition_closed[of c c]
      B.additive.unit_closed B.multiplicative.unit_closed Bc by auto
  show "(\<lambda>s\<in>A. c) \<in> A \<rightarrow>\<^sub>E B" using Bc by auto
  show "(\<lambda>s\<in>A. c) (addA a b) = addB ((\<lambda>s\<in>A. c) a) ((\<lambda>s\<in>A. c) b)" if "a \<in> A" "b \<in> A" for a b
    using that c by simp
  show "(\<lambda>s\<in>A. c) (multA a b) = multB ((\<lambda>s\<in>A. c) a) ((\<lambda>s\<in>A. c) b)" if "a \<in> A" "b \<in> A" for a b
    using that c by simp
  show "(\<lambda>s\<in>A. c) zeroA = zeroB" "(\<lambda>s\<in>A. c) oneA = oneB"
    using c by simp_all
qed

lemma bij_betw_factor:
  assumes g: "bij_betw g Q A" and k: "bij_betw k Q B" and eq: "\<And>q. q \<in> Q \<Longrightarrow> F (g q) = k q"
  shows "bij_betw F A B"
proof -
  have gA: "g ` Q = A" and kB: "k ` Q = B"
    using g k by (auto simp: bij_betw_def)
  have "inj_on F A"
  proof (rule inj_onI)
    fix a a' assume a: "a \<in> A" "a' \<in> A" "F a = F a'"
    then obtain q q' where q: "q \<in> Q" "a = g q" "q' \<in> Q" "a' = g q'" using gA by blast
    then have "k q = k q'" using a(3) eq by simp
    then have "q = q'" using k q by (auto simp: bij_betw_def inj_on_def)
    then show "a = a'" using q by simp
  qed
  moreover have "F ` A = B"
  proof -
    have "F ` A = (\<lambda>q. F (g q)) ` Q" using gA by auto
    also have "\<dots> = k ` Q" using eq by auto
    finally show ?thesis using kB by simp
  qed
  ultimately show ?thesis by (simp add: bij_betw_def)
qed


lemma ring_isomorphism_identity:
  assumes "ring A addA multA zeroA oneA"
  shows "ring_isomorphism (identity A) A addA multA zeroA oneA A addA multA zeroA oneA"
proof (rule ring_isomorphismI[OF assms assms])
  interpret A: ring A addA multA zeroA oneA by fact
  show "identity A \<in> A \<rightarrow>\<^sub>E A" by auto
  show "identity A (addA a b) = addA (identity A a) (identity A b)" if "a \<in> A" "b \<in> A" for a b
    using that by simp
  show "identity A (multA a b) = multA (identity A a) (identity A b)" if "a \<in> A" "b \<in> A" for a b
    using that by simp
  show "identity A zeroA = zeroA" "identity A oneA = oneA" by simp_all
  show "bij_betw (identity A) A A" by (auto simp: bij_betw_def inj_on_def)
qed

lemma ring_isomorphism_compose:
  assumes e: "ring_isomorphism \<eta> A addA multA zeroA oneA B addB multB zeroB oneB"
    and t: "ring_isomorphism \<theta> B addB multB zeroB oneB C addC multC zeroC oneC"
  shows "ring_isomorphism (compose A \<theta> \<eta>) A addA multA zeroA oneA C addC multC zeroC oneC"
proof -
  have hom: "ring_homomorphism (compose A \<theta> \<eta>) A addA multA zeroA oneA C addC multC zeroC oneC"
    by (rule comp_ring_morphisms[OF ring_isomorphism.axioms(1)[OF e] ring_isomorphism.axioms(1)[OF t]])
  have be: "bij_betw \<eta> A B" and bt: "bij_betw \<theta> B C"
    using ring_isomorphism.axioms(2)[OF e] ring_isomorphism.axioms(2)[OF t]
    by (simp_all add: bijective_map_def bijective_def)
  have "bij_betw (\<theta> \<circ> \<eta>) A C" by (rule bij_betw_trans[OF be bt])
  moreover have "bij_betw (compose A \<theta> \<eta>) A C = bij_betw (\<theta> \<circ> \<eta>) A C"
    by (rule bij_betw_cong) (simp add: compose_eq)
  ultimately have "bij_betw (compose A \<theta> \<eta>) A C" by simp
  then show ?thesis
    using hom ring_homomorphism.axioms(1)[OF hom]
    by (simp add: ring_isomorphism_def bijective_map_def bijective_def)
qed

lemma (in ring) minus_eq_zero_imp_eq:
  assumes "a \<in> R" "c \<in> R" "a - c = \<zero>"
  shows "a = c"
proof -
  have "a = a + (- c + c)" using assms(1,2) by simp
  also have "\<dots> = (a + (- c)) + c" using assms(1,2) by (simp add: additive.associative)
  also have "\<dots> = \<zero> + c" by (simp only: assms(3))
  also have "\<dots> = c" using assms(2) by simp
  finally show ?thesis .
qed

section \<open>Commutative rings whose spectrum is a single point\<close>

context comm_ring
begin

lemma point_ring_zariski:
  assumes spec: "Spec = {\<mm>}"
  shows "is_zariski_open U \<longleftrightarrow> U = {} \<or> U = {\<mm>}"
proof
  assume "is_zariski_open U"
  then have "U \<subseteq> Spec" unfolding is_zariski_open_def by (rule generated_topology_subset)
  then show "U = {} \<or> U = {\<mm>}" unfolding spec by blast
next
  assume "U = {} \<or> U = {\<mm>}"
  then show "is_zariski_open U" using is_zariski_open_empty is_zariski_open_Spec spec by auto
qed

lemma point_ring_local:
  assumes spec: "Spec = {\<mm>}"
    and units: "\<And>s. s \<in> R \<Longrightarrow> s \<notin> \<mm> \<Longrightarrow> \<exists>t\<in>R. s \<cdot> t = \<one>"
  shows "local_ring R (+) (\<cdot>) \<zero> \<one>"
proof -
  have m: "\<mm> \<in> Spec" using spec by simp
  interpret pi: pr_ideal R \<mm> "(+)" "(\<cdot>)" \<zero> \<one> using spectrum_imp_pr[OF m] .
  have ml: "lideal \<mm> R (+) (\<cdot>) \<zero> \<one>" using pi.ideal_axioms ideal_iff_lideal by blast
  have sub: "I \<subseteq> \<mm>" if I: "lideal I R (+) (\<cdot>) \<zero> \<one>" and ne: "I \<noteq> R" for I
  proof
    fix z assume z: "z \<in> I"
    interpret I: lideal I R "(+)" "(\<cdot>)" \<zero> \<one> by fact
    have zR: "z \<in> R" using z I.subset by blast
    show "z \<in> \<mm>"
    proof (rule ccontr)
      assume "z \<notin> \<mm>"
      then obtain t where t: "t \<in> R" "z \<cdot> t = \<one>" using units zR by blast
      then have "t \<cdot> z = \<one>" using comm_mult zR by simp
      then have "\<one> \<in> I" using I.lideal[OF t(1) z] by simp
      then show False using I.has_one_imp_equal ne by blast
    qed
  qed
  have mx: "max_lideal \<mm> R (+) (\<cdot>) \<zero> \<one>"
  proof (intro max_lideal.intro ml max_lideal_axioms.intro)
    show "\<mm> \<noteq> R" by (rule pi.carrier_neq)
    show "\<mm> = \<aa>" if "lideal \<aa> R (+) (\<cdot>) \<zero> \<one>" "\<aa> \<noteq> R" "\<mm> \<subseteq> \<aa>" for \<aa>
      using sub[OF that(1,2)] that(3) by blast
  qed
  have eq: "I = \<mm>" if "max_lideal I R (+) (\<cdot>) \<zero> \<one>" for I
  proof -
    interpret I: max_lideal I R "(+)" "(\<cdot>)" \<zero> \<one> by fact
    have "I \<subseteq> \<mm>" using sub[OF I.lideal_axioms I.neq_ring] .
    then show ?thesis using I.is_max[OF ml pi.carrier_neq] by blast
  qed
  show ?thesis
  proof (intro local_ring.intro local_ring_axioms.intro ring_axioms)
    show "I = J" if "max_lideal I R (+) (\<cdot>) \<zero> \<one>" "max_lideal J R (+) (\<cdot>) \<zero> \<one>" for I J
      using eq[OF that(1)] eq[OF that(2)] by simp
    show "\<exists>\<ww>. max_lideal \<ww> R (+) (\<cdot>) \<zero> \<one>" using mx by blast
  qed
qed

lemma sheaf_spec_point_iso:
  assumes spec: "Spec = {\<mm>}"
    and units: "\<And>s. s \<in> R \<Longrightarrow> s \<notin> \<mm> \<Longrightarrow> \<exists>t\<in>R. s \<cdot> t = \<one>"
  shows "ring_isomorphism
     (\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. quotient_ring.frac (R \<setminus> \<mm>) R (+) (\<cdot>) \<zero> r \<one>)
     R (+) (\<cdot>) \<zero> \<one>
     (sheaf_spec {\<mm>}) (add_sheaf_spec {\<mm>}) (mult_sheaf_spec {\<mm>})
     (zero_sheaf_spec {\<mm>}) (one_sheaf_spec {\<mm>})"
proof (rule ring_isomorphismI)
  have m: "\<mm> \<in> Spec" using spec by simp
  interpret qr: quotient_ring "R \<setminus> \<mm>" R "(+)" "(\<cdot>)" \<zero> \<one>
    using spectrum_imp_cxt_quotient_ring[OF m] .
  interpret pi: pr_ideal R \<mm> "(+)" "(\<cdot>)" \<zero> \<one> using spectrum_imp_pr[OF m] .
  have op: "is_zariski_open {\<mm>}" using is_zariski_open_Spec spec by simp
  show "ring R (+) (\<cdot>) \<zero> \<one>" by (rule ring_axioms)
  show "ring (sheaf_spec {\<mm>}) (add_sheaf_spec {\<mm>}) (mult_sheaf_spec {\<mm>})
     (zero_sheaf_spec {\<mm>}) (one_sheaf_spec {\<mm>})"
    using sheaf_spec_on_open_is_comm_ring[OF op] by (simp add: comm_ring_def)
  have one: "\<one> \<in> R \<setminus> \<mm>" by (rule qr.sub_unit_closed)
  have k_in: "(\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) \<in> sheaf_spec {\<mm>}" if r: "r \<in> R" for r
  proof -
    have c: "qr.frac r \<one> \<in> pi.carrier_local_ring_at"
      using frac_in_carrier_local[OF m r, of \<one>] one by simp
    have lf: "is_locally_frac (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) {\<mm>}"
      unfolding is_locally_frac_def
      by (rule exI[where x=r], rule exI[where x=\<one>]) (use r one in auto)
    have "is_regular (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) {\<mm>}"
      unfolding is_regular_def using op lf by blast
    then show ?thesis unfolding sheaf_spec_def using c by auto
  qed
  have kr: "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r = (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>)" if "r \<in> R" for r
    using that by simp
  show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) \<in> R \<rightarrow>\<^sub>E sheaf_spec {\<mm>}"
    using k_in by auto
  show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) (r + r') =
        add_sheaf_spec {\<mm>} ((\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r)
          ((\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r')" if rr: "r \<in> R" "r' \<in> R" for r r'
  proof -
    have "qr.add_rel (qr.frac r \<one>) (qr.frac r' \<one>) = qr.frac (r + r') \<one>"
      using qr.add_rel_frac[of r \<one> r' \<one>] rr one by simp
    then show ?thesis
      unfolding kr[OF rr(1)] kr[OF rr(2)] kr[OF additive.composition_closed[OF rr]]
        add_sheaf_spec_def
      by (intro restrict_ext) simp
  qed
  show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) (r \<cdot> r') =
        mult_sheaf_spec {\<mm>} ((\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r)
          ((\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r')" if rr: "r \<in> R" "r' \<in> R" for r r'
  proof -
    have "qr.mult_rel (qr.frac r \<one>) (qr.frac r' \<one>) = qr.frac (r \<cdot> r') \<one>"
      using qr.mult_rel_frac[of r \<one> r' \<one>] rr one by simp
    then show ?thesis
      unfolding kr[OF rr(1)] kr[OF rr(2)] kr[OF multiplicative.composition_closed[OF rr]]
        mult_sheaf_spec_def
      by (intro restrict_ext) simp
  qed
  show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) \<zero> = zero_sheaf_spec {\<mm>}"
    unfolding zero_sheaf_spec_def kr[OF additive.unit_closed]
    by (intro restrict_ext) (simp add: qr.zero_rel_def)
  show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) \<one> = one_sheaf_spec {\<mm>}"
    unfolding one_sheaf_spec_def kr[OF multiplicative.unit_closed]
    by (intro restrict_ext) (simp add: qr.one_rel_def)
  have inj: "r = r'" if rr: "r \<in> R" "r' \<in> R"
    and eq: "(\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) = (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r' \<one>)" for r r'
  proof -
    have fe: "qr.frac r \<one> = qr.frac r' \<one>" using fun_cong[OF eq, of \<mm>] by simp
    obtain s1 where s1: "s1 \<in> R \<setminus> \<mm>" "s1 \<cdot> (\<one> \<cdot> r - \<one> \<cdot> r') = \<zero>"
      by (rule qr.frac_eq_Ex[of r \<one> r' \<one>]) (use rr one fe in auto)
    then obtain t where t: "t \<in> R" "s1 \<cdot> t = \<one>" using units by blast
    have s1R: "s1 \<in> R" using s1(1) by simp
    have ts: "t \<cdot> s1 = \<one>" using t comm_mult s1R by simp
    have dR: "r - r' \<in> R" using rr by simp
    have z: "s1 \<cdot> (r - r') = \<zero>" using s1(2) rr by simp
    have "r - r' = (t \<cdot> s1) \<cdot> (r - r')" using ts dR by simp
    also have "\<dots> = t \<cdot> (s1 \<cdot> (r - r'))"
      using multiplicative.associative[OF t(1) s1R dR] .
    also have "\<dots> = \<zero>" using z t(1) by simp
    finally show ?thesis using minus_eq_zero_imp_eq[OF rr] by simp
  qed
  have surj: "\<exists>r\<in>R. s = (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>)" if s: "s \<in> sheaf_spec {\<mm>}" for s
  proof -
    have "s \<mm> \<in> pi.carrier_local_ring_at" using sec_has_right_codom[OF s] by simp
    then obtain r t where rt: "r \<in> R" "t \<in> R" "t \<notin> \<mm>" "s \<mm> = qr.frac r t"
      by (rule pi.frac_from_carrier_local)
    obtain u where u: "u \<in> R" "t \<cdot> u = \<one>" using units rt by blast
    have "t \<cdot> (r \<cdot> u) = t \<cdot> (u \<cdot> r)" using comm_mult rt u by simp
    also have "\<dots> = (t \<cdot> u) \<cdot> r" using multiplicative.associative[OF rt(2) u(1) rt(1)] by simp
    also have "\<dots> = r" using u rt by simp
    finally have e: "t \<cdot> (r \<cdot> u) = r" .
    have "qr.frac r t = qr.frac (r \<cdot> u) \<one>"
      by (rule qr.frac_eqI[of \<one>]) (use rt u one e in auto)
    then have "s \<mm> = qr.frac (r \<cdot> u) \<one>" using rt(4) by simp
    moreover have "s \<in> extensional {\<mm>}" using sec_is_extensional[OF s] .
    ultimately have "s = (\<lambda>\<pp>\<in>{\<mm>}. qr.frac (r \<cdot> u) \<one>)"
      by (intro extensionalityI[where A="{\<mm>}"]) auto
    then show ?thesis using rt u by blast
  qed
  show "bij_betw (\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) R (sheaf_spec {\<mm>})"
    unfolding bij_betw_def inj_on_def
  proof (intro conjI ballI impI)
    fix r r' assume "r \<in> R" "r' \<in> R"
      "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r = (\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) r'"
    then show "r = r'" using inj by simp
  next
    show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) ` R = sheaf_spec {\<mm>}"
    proof
      show "(\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) ` R \<subseteq> sheaf_spec {\<mm>}"
        using k_in by auto
      show "sheaf_spec {\<mm>} \<subseteq> (\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) ` R"
      proof
        fix s assume "s \<in> sheaf_spec {\<mm>}"
        then obtain r where "r \<in> R" "s = (\<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>)" using surj by blast
        then show "s \<in> (\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. qr.frac r \<one>) ` R" by (auto simp: image_iff)
      qed
    qed
  qed
qed

text \<open>A commutative ring in which every nonzero element is invertible (a field) has the
zero ideal as its only prime ideal.\<close>

lemma field_spectrum:
  assumes ne: "\<zero> \<noteq> \<one>"
    and inv: "\<And>s. s \<in> R \<Longrightarrow> s \<noteq> \<zero> \<Longrightarrow> \<exists>t\<in>R. s \<cdot> t = \<one>"
  shows "Spec = {{\<zero>}}"
proof -
  have pz: "pr_ideal R {\<zero>} (+) (\<cdot>) \<zero> \<one>"
  proof (intro pr_ideal.intro comm_ring_axioms ideal_0_R pr_ideal_axioms.intro)
    show "{\<zero>} \<noteq> R" using ne multiplicative.unit_closed by blast
    show "x \<in> {\<zero>} \<or> y \<in> {\<zero>}" if xy: "x \<in> R" "y \<in> R" "x \<cdot> y \<in> {\<zero>}" for x y
    proof (cases "x = \<zero>")
      case False
      then obtain t where t: "t \<in> R" "x \<cdot> t = \<one>" using inv xy(1) by blast
      have tx: "t \<cdot> x = \<one>" using t comm_mult xy(1) by simp
      have "y = (t \<cdot> x) \<cdot> y" using tx xy(2) by simp
      also have "\<dots> = t \<cdot> (x \<cdot> y)" using multiplicative.associative[OF t(1) xy(1,2)] .
      also have "\<dots> = \<zero>" using xy(3) t(1) by simp
      finally show ?thesis by simp
    qed simp
  qed
  have "I = {\<zero>}" if I: "pr_ideal R I (+) (\<cdot>) \<zero> \<one>" for I
  proof -
    interpret I: pr_ideal R I "(+)" "(\<cdot>)" \<zero> \<one> by fact
    have IR: "I \<subseteq> R" using ideal_implies_subset[OF I.ideal_axioms] .
    have "z = \<zero>" if z: "z \<in> I" for z
    proof (rule ccontr)
      assume "z \<noteq> \<zero>"
      then obtain t where t: "t \<in> R" "z \<cdot> t = \<one>" using inv z IR by blast
      have "t \<cdot> z = \<one>" using t comm_mult z IR by auto
      then have "\<one> \<in> I" using I.ideal(1)[OF t(1) z] by simp
      then show False using I.not_1 by simp
    qed
    moreover have "\<zero> \<in> I" using ideal_zero[OF I.ideal_axioms] .
    ultimately show ?thesis by blast
  qed
  then show ?thesis unfolding spectrum_def using pz by blast
qed

end

section \<open>Stalk at a point with a smallest open neighbourhood\<close>

context stalk
begin

lemma min_nbhd_iso:
  assumes N: "N \<in> I" and min: "\<And>U. U \<in> I \<Longrightarrow> N \<subseteq> U"
  shows "ring_isomorphism (\<lambda>s\<in>\<FF> N. class_of N s)
           (\<FF> N) (add_str N) (mult_str N) (zero_str N) (one_str N)
           carrier_stalk add_stalk mult_stalk (zero_stalk N) (one_stalk N)"
proof (rule ring_isomorphismI)
  have openN: "is_open N" "x \<in> N" using N index by auto
  show RN: "ring (\<FF> N) (add_str N) (mult_str N) (zero_str N) (one_str N)"
    using is_ring_from_is_homomorphism[OF openN(1)] .
  interpret RN: ring "\<FF> N" "add_str N" "mult_str N" "zero_str N" "one_str N" by fact
  show "ring carrier_stalk add_stalk mult_stalk (zero_stalk N) (one_stalk N)"
    using stalk_is_ring[OF openN] .
  have cl: "class_of N s \<in> carrier_stalk" if "s \<in> \<FF> N" for s
    using class_of_in_stalk[of N s] that N neighborhoods_eq by simp
  have rid: "\<rho> N N s = s" if "s \<in> \<FF> N" for s
    using identity_map openN that by simp
  show "(\<lambda>s\<in>\<FF> N. class_of N s) \<in> \<FF> N \<rightarrow>\<^sub>E carrier_stalk"
    using cl by auto
  show "(\<lambda>s\<in>\<FF> N. class_of N s) (add_str N s t) =
        add_stalk ((\<lambda>s\<in>\<FF> N. class_of N s) s) ((\<lambda>s\<in>\<FF> N. class_of N s) t)"
    if "s \<in> \<FF> N" "t \<in> \<FF> N" for s t
    unfolding add_stalk_def using add_rel_class_of[of N s N t N] that N rid by simp
  show "(\<lambda>s\<in>\<FF> N. class_of N s) (mult_str N s t) =
        mult_stalk ((\<lambda>s\<in>\<FF> N. class_of N s) s) ((\<lambda>s\<in>\<FF> N. class_of N s) t)"
    if "s \<in> \<FF> N" "t \<in> \<FF> N" for s t
    unfolding mult_stalk_def using mult_rel_class_of[of N s N t N] that N rid by simp
  show "(\<lambda>s\<in>\<FF> N. class_of N s) (zero_str N) = zero_stalk N"
    by (simp add: zero_stalk_def)
  show "(\<lambda>s\<in>\<FF> N. class_of N s) (one_str N) = one_stalk N"
    by (simp add: one_stalk_def)
  have inj: "s = t" if st: "s \<in> \<FF> N" "t \<in> \<FF> N" "class_of N s = class_of N t" for s t
  proof -
    obtain W where W: "W \<in> I" "W \<subseteq> N \<inter> N" "\<rho> N W s = \<rho> N W t"
      by (rule class_of_eqD[OF st(3)]) (use st N in auto)
    then have "W = N" using min by blast
    then show ?thesis using W(3) rid st by simp
  qed
  have surj: "\<exists>s\<in>\<FF> N. X = class_of N s" if "X \<in> carrier_stalk" for X
  proof -
    have "X \<in> carrier_direct_lim" using that carrier_stalk_def neighborhoods_eq by simp
    then obtain U s where U: "U \<in> I" "s \<in> \<FF> U" "X = class_of U s"
      by (rule carrier_direct_limE)
    have NU: "N \<subseteq> U" using min U(1) by blast
    have openU: "is_open U" using U(1) subset_of_opens by blast
    have rs: "\<rho> U N s \<in> \<FF> N"
      using is_map_from_is_homomorphism[OF openU openN(1) NU] U(2) by (simp add: map.map_closed)
    have "class_of U s = class_of N (\<rho> U N s)"
      by (rule class_of_eqI[where W=N]) (use U N NU rs rid in auto)
    then show ?thesis using U(3) rs by blast
  qed
  show "bij_betw (\<lambda>s\<in>\<FF> N. class_of N s) (\<FF> N) carrier_stalk"
    unfolding bij_betw_def inj_on_def using inj surj cl by (auto simp: image_iff) 
qed

lemma min_nbhd_local:
  assumes N: "N \<in> I" and min: "\<And>U. U \<in> I \<Longrightarrow> N \<subseteq> U"
    and loc: "local_ring (\<FF> N) (add_str N) (mult_str N) (zero_str N) (one_str N)"
    and U: "U \<in> I"
  shows "is_local U"
proof -
  have iso: "ring_isomorphism (\<lambda>s\<in>\<FF> N. class_of N s)
           (\<FF> N) (add_str N) (mult_str N) (zero_str N) (one_str N)
           carrier_stalk add_stalk mult_stalk (zero_stalk N) (one_stalk N)"
    by (rule min_nbhd_iso[OF N min])
  have "local_ring carrier_stalk add_stalk mult_stalk (zero_stalk N) (one_stalk N)"
    by (rule isomorphic_to_local_is_local[OF loc ring_isomorphism.inverse_ring_isomorphism[OF iso]])
  moreover have "zero_stalk U = zero_stalk N" "one_stalk U = one_stalk N"
    unfolding zero_stalk_def one_stalk_def
    using class_of_0_eq[OF U N] class_of_1_eq[OF U N] by auto
  ultimately show ?thesis unfolding is_local_def by simp
qed

end

section \<open>Isomorphisms of one-point locally ringed spaces\<close>

lemma one_point_iso_locally_ringed_spaces:
  fixes x :: 'a and y :: 'c and b :: 'b and d :: 'd
  assumes LX: "locally_ringed_space {x} isX OX \<rho>X b addX multX zeroX oneX"
    and LY: "locally_ringed_space {y} isY OY \<rho>Y d addY multY zeroY oneY"
    and h: "ring_isomorphism h (OY {y}) (addY {y}) (multY {y}) (zeroY {y}) (oneY {y})
                              (OX {x}) (addX {x}) (multX {x}) (zeroX {x}) (oneX {x})"
  defines "f \<equiv> \<lambda>z\<in>{x}. y"
    and "\<phi> \<equiv> \<lambda>V. if V = {y} then h else (\<lambda>s\<in>OY V. b)"
  shows "iso_locally_ringed_spaces {x} isX OX \<rho>X b addX multX zeroX oneX
           {y} isY OY \<rho>Y d addY multY zeroY oneY f \<phi>"
proof -
  interpret X: locally_ringed_space "{x}" isX OX \<rho>X b addX multX zeroX oneX by fact
  interpret Y: locally_ringed_space "{y}" isY OY \<rho>Y d addY multY zeroY oneY by fact
  interpret h: ring_isomorphism h "OY {y}" "addY {y}" "multY {y}" "zeroY {y}" "oneY {y}"
                              "OX {x}" "addX {x}" "multX {x}" "zeroX {x}" "oneX {x}" by fact
  have opX: "isX U \<longleftrightarrow> U = {} \<or> U = {x}" for U
    using X.open_imp_subset[of U] X.open_empty X.open_space by blast
  have opY: "isY U \<longleftrightarrow> U = {} \<or> U = {y}" for U
    using Y.open_imp_subset[of U] Y.open_empty Y.open_space by blast
  have fx: "f x = y" by (simp add: f_def)
  have pre [simp]: "f \<^sup>\<inverse> {x} {y} = {x}" "f \<^sup>\<inverse> {x} {} = {}"
    by (auto simp: f_def)
  have ne [simp]: "{} \<noteq> {y}" by simp
  have cm: "continuous_map {x} isX {y} isY f"
  proof (intro continuous_map.intro continuous_map_axioms.intro
      X.topological_space_axioms Y.topological_space_axioms)
    show "Set_Theory.map f {x} {y}" by (simp add: Set_Theory.map_def f_def)
    show "isX (f \<^sup>\<inverse> {x} U)" if "isY U" for U
      using that opY opX by auto
  qed
  interpret im: im_sheaf "{x}" isX OX \<rho>X b addX multX zeroX oneX "{y}" isY f
    by (intro im_sheaf.intro X.sheaf_of_rings_axioms cm)
  have imP: "presheaf_of_rings {y} isY im.im_sheaf im.im_sheaf_morphisms b
               im.add_im_sheaf im.mult_im_sheaf im.zero_im_sheaf im.one_im_sheaf"
    by (rule im.im_sheaf_is_presheaf)
  have im_y [simp]: "im.im_sheaf {y} = OX {x}" "im.add_im_sheaf {y} = addX {x}"
    "im.mult_im_sheaf {y} = multX {x}" "im.zero_im_sheaf {y} = zeroX {x}"
    "im.one_im_sheaf {y} = oneX {x}"
    by (simp_all add: im.im_sheaf_def im.add_im_sheaf_def im.mult_im_sheaf_def
        im.zero_im_sheaf_def im.one_im_sheaf_def)
  have OXe: "OX {} = {b}" by (rule X.ring_of_empty)
  have OYe: "OY {} = {d}" by (rule Y.ring_of_empty)
  have im_e [simp]: "im.im_sheaf {} = {b}"
    by (simp add: im.im_sheaf_def OXe)
  have im_mor [simp]: "im.im_sheaf_morphisms {y} {y} = \<rho>X {x} {x}"
    "im.im_sheaf_morphisms {y} {} = \<rho>X {x} {}" "im.im_sheaf_morphisms {} {} = \<rho>X {} {}"
    by (simp_all add: im.im_sheaf_morphisms_def)
  have ringYe: "ring (OY {}) (addY {}) (multY {}) (zeroY {}) (oneY {})"
    by (rule Y.is_ring_from_is_homomorphism[OF Y.open_empty])
  have ringIe: "ring (im.im_sheaf {}) (im.add_im_sheaf {}) (im.mult_im_sheaf {})
      (im.zero_im_sheaf {}) (im.one_im_sheaf {})"
    by (rule presheaf_of_rings.is_ring_from_is_homomorphism[OF imP Y.open_empty])
  have rX: "\<rho>X {x} {x} p = p" if "p \<in> OX {x}" for p
    using X.identity_map[OF X.open_space that] .
  have rXe: "\<rho>X {x} {} p = b" if "p \<in> OX {x}" for p
    using map.map_closed[OF X.is_map_from_is_homomorphism[OF X.open_space X.open_empty], of p]
      that OXe by auto
  have rXee: "\<rho>X {} {} b = b"
    using X.identity_map[OF X.open_empty, of b] OXe by simp
  have rY: "\<rho>Y {y} {y} q = q" if "q \<in> OY {y}" for q
    using Y.identity_map[OF Y.open_space that] .
  have rYe: "\<rho>Y {y} {} q = d" if "q \<in> OY {y}" for q
    using map.map_closed[OF Y.is_map_from_is_homomorphism[OF Y.open_space Y.open_empty], of q]
      that OYe by auto
  have rYee: "\<rho>Y {} {} d = d"
    using Y.identity_map[OF Y.open_empty, of d] OYe by simp
  have hq: "h q \<in> OX {x}" if "q \<in> OY {y}" for q
    using that by (rule h.map_closed)

  have mor: "morphism_presheaves_of_rings {y} isY OY \<rho>Y d addY multY zeroY oneY
        im.im_sheaf im.im_sheaf_morphisms b
        im.add_im_sheaf im.mult_im_sheaf im.zero_im_sheaf im.one_im_sheaf \<phi>"
  proof (intro morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms.intro
      Y.presheaf_of_rings_axioms imP)
    fix U assume "isY U"
    then consider "U = {y}" | "U = {}" using opY by blast
    then show "ring_homomorphism (\<phi> U) (OY U) (addY U) (multY U) (zeroY U) (oneY U)
        (im.im_sheaf U) (im.add_im_sheaf U) (im.mult_im_sheaf U) (im.zero_im_sheaf U)
        (im.one_im_sheaf U)"
    proof cases
      case 1
      then show ?thesis using h.ring_homomorphism_axioms by (simp add: \<phi>_def)
    next
      case 2
      show ?thesis unfolding 2 \<phi>_def using trivial_ring_hom[OF ringYe ringIe im_e] by simp
    qed
  next
    fix U V q assume "isY U" "isY V" "V \<subseteq> U" "q \<in> OY U"
    then consider "U = {y}" "V = {y}" | "U = {y}" "V = {}" | "U = {}" "V = {}"
      using opY by blast
    then show "(im.im_sheaf_morphisms U V \<circ> \<phi> U) q = (\<phi> V \<circ> \<rho>Y U V) q"
    proof cases
      case 1
      then show ?thesis using \<open>q \<in> OY U\<close> rX hq rY by (simp add: \<phi>_def)
    next
      case 2
      then show ?thesis using \<open>q \<in> OY U\<close> rXe hq rYe OYe by (simp add: \<phi>_def)
    next
      case 3
      then show ?thesis using \<open>q \<in> OY U\<close> rXee rYee OYe by (simp add: \<phi>_def)
    qed
  qed

  interpret mrs: morphism_ringed_spaces "{x}" isX OX \<rho>X b addX multX zeroX oneX
      "{y}" isY OY \<rho>Y d addY multY zeroY oneY f \<phi>
    by (intro morphism_ringed_spaces.intro im.im_sheaf_axioms Y.ringed_space_axioms
        morphism_ringed_spaces_axioms.intro morphism_sheaves_of_rings.intro mor)

  interpret ims: ind_mor_btw_stalks "{x}" isX OX \<rho>X b addX multX zeroX oneX
      "{y}" isY OY \<rho>Y d addY multY zeroY oneY f \<phi> x
    by (intro ind_mor_btw_stalks.intro mrs.morphism_ringed_spaces_axioms
        ind_mor_btw_stalks_axioms.intro) simp

  interpret sx: stalk "{x}" isX OX \<rho>X b addX multX zeroX oneX "{U. isX U \<and> x \<in> U}" x
  proof qed (use opX in auto)
  interpret sy: stalk "{y}" isY OY \<rho>Y d addY multY zeroY oneY "{U. isY U \<and> y \<in> U}" y
  proof qed (use opY in auto)

  have Nx: "{x} \<in> {U. isX U \<and> x \<in> U}" and minx: "\<And>U. U \<in> {U. isX U \<and> x \<in> U} \<Longrightarrow> {x} \<subseteq> U"
    using opX by auto
  have Ny: "{y} \<in> {U. isY U \<and> y \<in> U}" and miny: "\<And>U. U \<in> {U. isY U \<and> y \<in> U} \<Longrightarrow> {y} \<subseteq> U"
    using opY by auto
  have cX: "bij_betw (\<lambda>s\<in>OX {x}. sx.class_of {x} s) (OX {x}) sx.carrier_stalk"
    using ring_isomorphism.axioms(2)[OF sx.min_nbhd_iso[OF Nx minx]]
    by (simp add: bijective_map_def bijective_def)
  have cY: "bij_betw (\<lambda>s\<in>OY {y}. sy.class_of {y} s) (OY {y}) sy.carrier_stalk"
    using ring_isomorphism.axioms(2)[OF sy.min_nbhd_iso[OF Ny miny]]
    by (simp add: bijective_map_def bijective_def)
  have hb: "bij_betw h (OY {y}) (OX {x})" by (rule h.bijective)

  have ind_eq: "ims.induced_morphism ((\<lambda>s\<in>OY {y}. sy.class_of {y} s) q)
        = ((\<lambda>s\<in>OX {x}. sx.class_of {x} s) \<circ> h) q" if q: "q \<in> OY {y}" for q
  proof -
    have mem: "({y}, q) \<in> sy.class_of {y} q"
      unfolding sy.class_of_def
      by (rule equivalence.Class_self[OF sy.rel_is_equivalence]) (use q Ny in auto)
    have car: "sy.class_of {y} q \<in> sy.carrier_stalk"
      using bij_betw_apply[OF cY q] q by simp
    have "ims.induced_morphism (sy.class_of {y} q)
        = sx.class_of (f \<^sup>\<inverse> {x} (fst ({y}, q))) (\<phi> (fst ({y}, q)) (snd ({y}, q)))"
      using ims.induced_morphism_eval[unfolded fx, OF car mem] .
    then show ?thesis using q hq by (simp add: \<phi>_def)
  qed
  have ind_bij: "bij_betw ims.induced_morphism sy.carrier_stalk sx.carrier_stalk"
    by (rule bij_betw_factor[OF cY bij_betw_trans[OF hb cX] ind_eq])

  have local_mor: "ims.is_local V ims.induced_morphism" if "isY V" "f x \<in> V" for V
  proof -
    have V: "V = {y}" using that opY fx by auto
    have hom: "ring_homomorphism ims.induced_morphism
        sy.carrier_stalk sy.add_stalk sy.mult_stalk (sy.zero_stalk V) (sy.one_stalk V)
        sx.carrier_stalk sx.add_stalk sx.mult_stalk
        (sx.zero_stalk (f \<^sup>\<inverse> {x} V)) (sx.one_stalk (f \<^sup>\<inverse> {x} V))"
      using ims.ring_homomorphism_induced_morphism[unfolded fx, OF that(1)] that(2) fx by simp
    have iso: "ring_isomorphism ims.induced_morphism
        sy.carrier_stalk sy.add_stalk sy.mult_stalk (sy.zero_stalk V) (sy.one_stalk V)
        sx.carrier_stalk sx.add_stalk sx.mult_stalk
        (sx.zero_stalk (f \<^sup>\<inverse> {x} V)) (sx.one_stalk (f \<^sup>\<inverse> {x} V))"
      using hom ind_bij ring_homomorphism.axioms(1)[OF hom]
      by (simp add: ring_isomorphism_def bijective_map_def bijective_def)
    have loc: "local_ring sy.carrier_stalk sy.add_stalk sy.mult_stalk
        (sy.zero_stalk V) (sy.one_stalk V)"
      using Y.stalks_are_local[of y V] V opY sy.is_local_def sy.neighborhoods_eq by simp
    show ?thesis
      unfolding ims.is_local_def fx
      by (rule iso_is_local_ring_morphism[OF loc iso])
  qed

  have mlrs: "morphism_locally_ringed_spaces {x} isX OX \<rho>X b addX multX zeroX oneX
           {y} isY OY \<rho>Y d addY multY zeroY oneY f \<phi>"
    by (intro morphism_locally_ringed_spaces.intro mrs.morphism_ringed_spaces_axioms
        morphism_locally_ringed_spaces_axioms.intro) (use local_mor in auto)

  have bm: "bijective_map f {x} {y}"
    by (simp add: bijective_map_def bijective_def Set_Theory.map_def f_def bij_betw_def)
  have homeo: "homeomorphism {x} isX {y} isY f"
  proof (intro homeomorphism.intro cm bm continuous_map.intro continuous_map_axioms.intro
      X.topological_space_axioms Y.topological_space_axioms)
    show "Set_Theory.map (inverse_map f {x} {y}) {y} {x}"
      using bijective_map_preimage[OF bm] by (simp add: bijective_map_def)
    show "isY (inverse_map f {x} {y} \<^sup>\<inverse> {y} U)" if "isX U" for U
    proof -
      have "inverse_map f {x} {y} \<^sup>\<inverse> {y} U \<subseteq> {y}" by blast
      then show ?thesis using opY by blast
    qed
  qed

  define \<psi> where "\<psi> = (\<lambda>V. if V = {y} then restrict (inv_into (OY {y}) h) (OX {x})
                              else (\<lambda>s\<in>im.im_sheaf V. d))"
  have hinv: "ring_isomorphism (restrict (inv_into (OY {y}) h) (OX {x}))
       (OX {x}) (addX {x}) (multX {x}) (zeroX {x}) (oneX {x})
       (OY {y}) (addY {y}) (multY {y}) (zeroY {y}) (oneY {y})"
    by (rule h.inverse_ring_isomorphism)
  have hi1: "inv_into (OY {y}) h (h q) = q" if "q \<in> OY {y}" for q
    using that bij_betw_inv_into_left[OF hb] by simp
  have hi2: "h (inv_into (OY {y}) h p) = p" "inv_into (OY {y}) h p \<in> OY {y}"
    if "p \<in> OX {x}" for p
    using that bij_betw_inv_into_right[OF hb] bij_betw_apply[OF bij_betw_inv_into[OF hb]] by auto
  have mor': "morphism_presheaves_of_rings {y} isY
        im.im_sheaf im.im_sheaf_morphisms b
        im.add_im_sheaf im.mult_im_sheaf im.zero_im_sheaf im.one_im_sheaf
        OY \<rho>Y d addY multY zeroY oneY \<psi>"
  proof (intro morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms.intro
      Y.presheaf_of_rings_axioms imP)
    fix U assume "isY U"
    then consider "U = {y}" | "U = {}" using opY by blast
    then show "ring_homomorphism (\<psi> U)
        (im.im_sheaf U) (im.add_im_sheaf U) (im.mult_im_sheaf U) (im.zero_im_sheaf U)
        (im.one_im_sheaf U) (OY U) (addY U) (multY U) (zeroY U) (oneY U)"
    proof cases
      case 1
      then show ?thesis using ring_isomorphism.axioms(1)[OF hinv] by (simp add: \<psi>_def)
    next
      case 2
      show ?thesis unfolding 2 \<psi>_def using trivial_ring_hom[OF ringIe ringYe OYe] by simp
    qed
  next
    fix U V p assume "isY U" "isY V" "V \<subseteq> U" "p \<in> im.im_sheaf U"
    then consider "U = {y}" "V = {y}" | "U = {y}" "V = {}" | "U = {}" "V = {}"
      using opY by blast
    then show "(\<rho>Y U V \<circ> \<psi> U) p = (\<psi> V \<circ> im.im_sheaf_morphisms U V) p"
    proof cases
      case 1
      then show ?thesis using \<open>p \<in> im.im_sheaf U\<close> rX rY hi2 by (simp add: \<psi>_def)
    next
      case 2
      then show ?thesis using \<open>p \<in> im.im_sheaf U\<close> rXe rYe hi2 by (simp add: \<psi>_def)
    next
      case 3
      then show ?thesis using \<open>p \<in> im.im_sheaf U\<close> rXee rYee by (simp add: \<psi>_def)
    qed
  qed
  have inv_laws: "(\<forall>p\<in>im.im_sheaf U. (\<phi> U \<circ> \<psi> U) p = p) \<and> (\<forall>q\<in>OY U. (\<psi> U \<circ> \<phi> U) q = q)"
    if oU: "isY U" for U
  proof -
    consider "U = {y}" | "U = {}" using oU opY by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using hi1 hi2 hq by (simp add: \<phi>_def \<psi>_def)
    next
      case 2
      then show ?thesis using OYe by (simp add: \<phi>_def \<psi>_def)
    qed
  qed
  have iso_sh: "iso_sheaves_of_rings {y} isY OY \<rho>Y d addY multY zeroY oneY
        im.im_sheaf im.im_sheaf_morphisms b
        im.add_im_sheaf im.mult_im_sheaf im.zero_im_sheaf im.one_im_sheaf \<phi>"
    by (intro iso_sheaves_of_rings.intro iso_presheaves_of_rings.intro mor
        iso_presheaves_of_rings_axioms.intro exI[where x=\<psi>] conjI mor' allI impI)
       (use inv_laws in auto)
  show ?thesis
    by (intro iso_locally_ringed_spaces.intro mlrs iso_locally_ringed_spaces_axioms.intro
        homeo iso_sh)
qed

section \<open>An open point with a local one-prime ring of sections is an affine scheme\<close>

context sheaf_of_rings
begin

lemma open_point_stalk_local:
  assumes xo: "is_open {x}"
    and loc: "local_ring (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    and U: "is_open U" "x \<in> U"
  shows "stalk.is_local is_open \<FF> \<rho> add_str mult_str zero_str one_str (neighborhoods x) x U"
proof -
  have xS: "x \<in> S" using open_imp_subset[OF xo] by simp
  interpret st: stalk S is_open \<FF> \<rho> b add_str mult_str zero_str one_str
      "{U. is_open U \<and> x \<in> U}" x
  proof qed (use xS in auto)
  show ?thesis
    unfolding neighborhoods_def
    by (rule st.min_nbhd_local[where N="{x}"]) (use xo loc U in auto)
qed

theorem open_point_affine_scheme:
  fixes x :: 'a and R :: "'r set"
  assumes xo: "is_open {x}"
    and R: "comm_ring R addR multR zeroR oneR"
    and spec: "comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}"
    and units: "\<And>s. s \<in> R \<Longrightarrow> s \<notin> \<mm> \<Longrightarrow> \<exists>t\<in>R. multR s t = oneR"
    and g: "ring_isomorphism g (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
              R addR multR zeroR oneR"
  shows "\<exists>f \<phi>. affine_scheme R addR multR zeroR oneR {x}
           (ind_topology.ind_is_open S is_open {x})
           (ind_sheaf.ind_sheaf \<FF> {x}) (ind_sheaf.ind_ring_morphisms \<rho> {x}) b
           (ind_sheaf.ind_add_str add_str {x}) (ind_sheaf.ind_mult_str mult_str {x})
           (ind_sheaf.ind_zero_str zero_str {x}) (ind_sheaf.ind_one_str one_str {x}) f \<phi>"
proof -
  interpret R: comm_ring R addR multR zeroR oneR by fact
  interpret ish: ind_sheaf S is_open \<FF> \<rho> b add_str mult_str zero_str one_str "{x}"
    by unfold_locales (rule xo)
  let ?io = "ind_topology.ind_is_open S is_open {x}"
  have shX: "sheaf_of_rings {x} ?io ish.ind_sheaf ish.ind_ring_morphisms b
      ish.ind_add_str ish.ind_mult_str ish.ind_zero_str ish.ind_one_str"
    by (rule ish.ind_sheaf_is_sheaf)
  interpret sh: sheaf_of_rings "{x}" ?io ish.ind_sheaf ish.ind_ring_morphisms b
      ish.ind_add_str ish.ind_mult_str ish.ind_zero_str ish.ind_one_str by fact
  have ind_x [simp]: "ish.ind_sheaf {x} = \<FF> {x}" "ish.ind_add_str {x} = add_str {x}"
    "ish.ind_mult_str {x} = mult_str {x}" "ish.ind_zero_str {x} = zero_str {x}"
    "ish.ind_one_str {x} = one_str {x}"
    by (simp_all add: ish.ind_sheaf_def ish.ind_add_str_def ish.ind_mult_str_def
        ish.ind_zero_str_def ish.ind_one_str_def)
  have locR: "local_ring R addR multR zeroR oneR" by (rule R.point_ring_local[OF spec units])
  have locF: "local_ring (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    by (rule isomorphic_to_local_is_local[OF locR g])
  have iox: "?io {x}" by (rule sh.open_space)
  have LX: "locally_ringed_space {x} ?io ish.ind_sheaf ish.ind_ring_morphisms b
      ish.ind_add_str ish.ind_mult_str ish.ind_zero_str ish.ind_one_str"
  proof (intro locally_ringed_space.intro ringed_space.intro shX locally_ringed_space_axioms.intro)
    fix u U assume uU: "u \<in> U" "?io U"
    then have ux: "u = x" using sh.open_imp_subset by blast
    show "stalk.is_local ?io ish.ind_sheaf ish.ind_ring_morphisms ish.ind_add_str ish.ind_mult_str
        ish.ind_zero_str ish.ind_one_str (sh.neighborhoods u) u U"
      unfolding ux
      by (rule sh.open_point_stalk_local[OF iox]) (use locF uU ux in auto)
  qed
  have LY: "locally_ringed_space {\<mm>} R.is_zariski_open R.sheaf_spec R.sheaf_spec_morphisms R.\<O>b
      R.add_sheaf_spec R.mult_sheaf_spec R.zero_sheaf_spec R.one_sheaf_spec"
    using R.spec_is_locally_ringed_space spec by simp
  let ?k = "\<lambda>r\<in>R. \<lambda>\<pp>\<in>{\<mm>}. quotient_ring.frac (R \<setminus> \<mm>) R addR multR zeroR r oneR"
  have k: "ring_isomorphism ?k R addR multR zeroR oneR
     (R.sheaf_spec {\<mm>}) (R.add_sheaf_spec {\<mm>}) (R.mult_sheaf_spec {\<mm>})
     (R.zero_sheaf_spec {\<mm>}) (R.one_sheaf_spec {\<mm>})"
    by (rule R.sheaf_spec_point_iso[OF spec units])
  have kg: "ring_isomorphism (compose (\<FF> {x}) ?k g)
     (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
     (R.sheaf_spec {\<mm>}) (R.add_sheaf_spec {\<mm>}) (R.mult_sheaf_spec {\<mm>})
     (R.zero_sheaf_spec {\<mm>}) (R.one_sheaf_spec {\<mm>})"
    by (rule ring_isomorphism_compose[OF g k])
  define h where "h = restrict (inv_into (\<FF> {x}) (compose (\<FF> {x}) ?k g)) (R.sheaf_spec {\<mm>})"
  have h: "ring_isomorphism h
     (R.sheaf_spec {\<mm>}) (R.add_sheaf_spec {\<mm>}) (R.mult_sheaf_spec {\<mm>})
     (R.zero_sheaf_spec {\<mm>}) (R.one_sheaf_spec {\<mm>})
     (ish.ind_sheaf {x}) (ish.ind_add_str {x}) (ish.ind_mult_str {x})
     (ish.ind_zero_str {x}) (ish.ind_one_str {x})"
    unfolding h_def using ring_isomorphism.inverse_ring_isomorphism[OF kg] by simp
  have iso: "iso_locally_ringed_spaces {x} ?io ish.ind_sheaf ish.ind_ring_morphisms b
      ish.ind_add_str ish.ind_mult_str ish.ind_zero_str ish.ind_one_str
      {\<mm>} R.is_zariski_open R.sheaf_spec R.sheaf_spec_morphisms R.\<O>b
      R.add_sheaf_spec R.mult_sheaf_spec R.zero_sheaf_spec R.one_sheaf_spec
      (\<lambda>z\<in>{x}. \<mm>) (\<lambda>V. if V = {\<mm>} then h else (\<lambda>s\<in>R.sheaf_spec V. b))"
    by (rule one_point_iso_locally_ringed_spaces[OF LX LY h])
  have "affine_scheme R addR multR zeroR oneR {x} ?io ish.ind_sheaf ish.ind_ring_morphisms b
      ish.ind_add_str ish.ind_mult_str ish.ind_zero_str ish.ind_one_str
      (\<lambda>z\<in>{x}. \<mm>) (\<lambda>V. if V = {\<mm>} then h else (\<lambda>s\<in>R.sheaf_spec V. b))"
    by (intro affine_scheme.intro R LX) (use iso spec in simp)
  then show ?thesis by blast
qed

theorem open_points_scheme:
  assumes pts: "\<And>x. x \<in> S \<Longrightarrow> is_open {x}"
    and rings: "\<And>x. x \<in> S \<Longrightarrow> \<exists>(R :: 'r set) addR multR zeroR oneR \<mm> g.
        comm_ring R addR multR zeroR oneR
      \<and> comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}
      \<and> (\<forall>s\<in>R. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>R. multR s t = oneR))
      \<and> ring_isomorphism g (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
            R addR multR zeroR oneR"
  shows "scheme S is_open \<FF> \<rho> b add_str mult_str zero_str one_str (UNIV :: 'r set)"
proof (intro scheme.intro locally_ringed_space.intro ringed_space.intro sheaf_of_rings_axioms
    locally_ringed_space_axioms.intro scheme_axioms.intro)
  fix x U assume xU: "x \<in> U" "is_open U"
  then have xS: "x \<in> S" using open_imp_subset by blast
  obtain R :: "'r set" and addR multR zeroR oneR \<mm> g where
    R: "comm_ring R addR multR zeroR oneR"
    and spec: "comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}"
    and units: "\<forall>s\<in>R. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>R. multR s t = oneR)"
    and g: "ring_isomorphism g (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
            R addR multR zeroR oneR"
    using rings[OF xS] by (elim exE conjE) (rule that)
  have locR: "local_ring R addR multR zeroR oneR"
    by (rule comm_ring.point_ring_local[OF R spec]) (use units in blast)
  have locF: "local_ring (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    by (rule isomorphic_to_local_is_local[OF locR g])
  show "stalk.is_local is_open \<FF> \<rho> add_str mult_str zero_str one_str (neighborhoods x) x U"
    by (rule open_point_stalk_local[OF pts[OF xS] locF xU(2,1)])
next
  fix x assume xS: "x \<in> S"
  obtain R :: "'r set" and addR multR zeroR oneR \<mm> g where
    R: "comm_ring R addR multR zeroR oneR"
    and spec: "comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}"
    and units: "\<forall>s\<in>R. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>R. multR s t = oneR)"
    and g: "ring_isomorphism g (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
            R addR multR zeroR oneR"
    using rings[OF xS] by (elim exE conjE) (rule that)
  have "\<exists>f \<phi>. affine_scheme R addR multR zeroR oneR {x}
           (ind_topology.ind_is_open S is_open {x})
           (ind_sheaf.ind_sheaf \<FF> {x}) (ind_sheaf.ind_ring_morphisms \<rho> {x}) b
           (ind_sheaf.ind_add_str add_str {x}) (ind_sheaf.ind_mult_str mult_str {x})
           (ind_sheaf.ind_zero_str zero_str {x}) (ind_sheaf.ind_one_str one_str {x}) f \<phi>"
    by (rule open_point_affine_scheme[OF pts[OF xS] R spec _ g]) (use units in blast)
  then show "\<exists>U. x \<in> U \<and> is_open U \<and>
       (\<exists>R add mult zero one f \<phi>\<^sub>f. R \<subseteq> (UNIV :: 'r set) \<and> comm_ring R add mult zero one \<and>
           affine_scheme R add mult zero one U (ind_topology.ind_is_open S is_open U)
            (ind_sheaf.ind_sheaf \<FF> U) (ind_sheaf.ind_ring_morphisms \<rho> U) b
            (ind_sheaf.ind_add_str add_str U) (ind_sheaf.ind_mult_str mult_str U)
            (ind_sheaf.ind_zero_str zero_str U) (ind_sheaf.ind_one_str one_str U) f \<phi>\<^sub>f)"
    using pts[OF xS] R by (intro exI[where x="{x}"]) blast
qed

text \<open>The special case in which the ring of the affine chart at \<open>x\<close> is the ring of
sections over \<open>{x}\<close> itself.\<close>

corollary open_points_scheme_self:
  assumes pts: "\<And>x. x \<in> S \<Longrightarrow> is_open {x}"
    and comm: "\<And>x. x \<in> S \<Longrightarrow>
        comm_ring (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    and prime: "\<And>x. x \<in> S \<Longrightarrow> \<exists>\<mm>.
        comm_ring.spectrum (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x}) = {\<mm>}
      \<and> (\<forall>s\<in>\<FF> {x}. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>\<FF> {x}. mult_str {x} s t = one_str {x}))"
  shows "scheme S is_open \<FF> \<rho> b add_str mult_str zero_str one_str (UNIV :: 'b set)"
proof (rule open_points_scheme[OF pts])
  fix x assume xS: "x \<in> S"
  obtain \<mm> where m:
    "comm_ring.spectrum (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x}) = {\<mm>}"
    "\<forall>s\<in>\<FF> {x}. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>\<FF> {x}. mult_str {x} s t = one_str {x})"
    using prime[OF xS] by blast
  have id: "ring_isomorphism (identity (\<FF> {x}))
      (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
      (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    by (rule ring_isomorphism_identity[OF is_ring_from_is_homomorphism[OF pts[OF xS]]])
  show "\<exists>(R :: 'b set) addR multR zeroR oneR \<mm> g.
        comm_ring R addR multR zeroR oneR
      \<and> comm_ring.spectrum R addR multR zeroR oneR = {\<mm>}
      \<and> (\<forall>s\<in>R. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>R. multR s t = oneR))
      \<and> ring_isomorphism g (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
            R addR multR zeroR oneR"
    using comm[OF xS] m id by blast
qed

text \<open>The special case of fields: only the rings over the singletons are constrained.
The rings of sections over larger open sets need not even be commutative, beyond what
the locale \<open>sheaf_of_rings\<close> itself demands.\<close>

corollary open_points_scheme_field:
  assumes pts: "\<And>x. x \<in> S \<Longrightarrow> is_open {x}"
    and comm: "\<And>x. x \<in> S \<Longrightarrow>
        comm_ring (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})"
    and ne: "\<And>x. x \<in> S \<Longrightarrow> zero_str {x} \<noteq> one_str {x}"
    and inv: "\<And>x s. x \<in> S \<Longrightarrow> s \<in> \<FF> {x} \<Longrightarrow> s \<noteq> zero_str {x} \<Longrightarrow>
        \<exists>t\<in>\<FF> {x}. mult_str {x} s t = one_str {x}"
  shows "scheme S is_open \<FF> \<rho> b add_str mult_str zero_str one_str (UNIV :: 'b set)"
proof (rule open_points_scheme_self[OF pts comm])
  fix x assume xS: "x \<in> S"
  have "comm_ring.spectrum (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x})
      = {{zero_str {x}}}"
    by (rule comm_ring.field_spectrum[OF comm[OF xS] ne[OF xS] inv[OF xS]])
  then show "\<exists>\<mm>.
        comm_ring.spectrum (\<FF> {x}) (add_str {x}) (mult_str {x}) (zero_str {x}) (one_str {x}) = {\<mm>}
      \<and> (\<forall>s\<in>\<FF> {x}. s \<notin> \<mm> \<longrightarrow> (\<exists>t\<in>\<FF> {x}. mult_str {x} s t = one_str {x}))"
    using inv[OF xS] by (intro exI[where x="{zero_str {x}}"]) auto
qed

end

end
