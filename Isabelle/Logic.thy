theory Logic imports Main begin

datatype form =
  Pro \<open>nat\<close> (\<open>\<cdot>\<close>) |
  Falsity (\<open>\<bottom>\<close>) |
  Imp \<open>form\<close> \<open>form\<close> (infix \<open>\<rightarrow>\<close> 0)

primrec semantics (infix \<open>\<Turnstile>\<close> 0) where
  \<open>(I \<Turnstile> \<cdot> n) = I n\<close> |
  \<open>(I \<Turnstile> \<bottom>) = False\<close> |
  \<open>(I \<Turnstile> (p \<rightarrow> q)) = ((I \<Turnstile> p) \<longrightarrow> (I \<Turnstile> q))\<close>

abbreviation sc (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>I\<rbrakk> X Y \<equiv> (\<forall>p \<in> set X. (I \<Turnstile> p)) \<longrightarrow> (\<exists>q \<in> set Y. (I \<Turnstile> q))\<close>

inductive SC (\<open>_ \<then> _\<close> 0) where
  Fls_L: \<open>\<bottom> # _ \<then> _\<close> |
  Imp_L: \<open>(p \<rightarrow> q) # X \<then> Y\<close> if \<open>X \<then> p # Y\<close> and \<open>q # X \<then> Y\<close> |
  Imp_R: \<open>X \<then> (p \<rightarrow> q) # Y\<close> if \<open>p # X \<then> q # Y\<close> |
  Set_L: \<open>X' \<then> Y\<close> if \<open>X \<then> Y\<close> and \<open>set X' = set X\<close> |
  Set_R: \<open>X \<then> Y'\<close> if \<open>X \<then> Y\<close> and \<open>set Y' = set Y\<close> |
  Basic: \<open>p # _ \<then> p # _\<close>

function mp where
  \<open>mp A B (\<cdot>n # C) [] = mp (n # A) B C []\<close> |
  \<open>mp A B C (\<cdot>n # D) = mp A (n # B) C D\<close> |
  \<open>mp _ _ (\<bottom> # _) [] = True\<close> |
  \<open>mp A B C (\<bottom> # D) = mp A B C D\<close> |
  \<open>mp A B ((p \<rightarrow> q) # C) [] = (mp A B C [p] \<and> mp A B (q # C) [])\<close> |
  \<open>mp A B C ((p \<rightarrow> q) # D) = mp A B (p # C) (q # D)\<close> |
  \<open>mp A B [] [] = (set A \<inter> set B \<noteq> {})\<close>
  by pat_completeness simp_all

termination
  by (relation \<open>measure (\<lambda>(_, _, C, D). 2 * (\<Sum>p \<leftarrow> C @ D. size p) + length (C @ D))\<close>) simp_all

lemma main: \<open>(\<forall>I. \<lbrakk>I\<rbrakk> (map \<cdot> A @ C) (map \<cdot> B @ D)) \<longleftrightarrow> mp A B C D\<close>
  by (induct rule: mp.induct) (simp_all, blast, meson, fast)

lemma MP: \<open>mp A B C D \<Longrightarrow> set X \<supseteq> set (map \<cdot> A @ C) \<Longrightarrow> set Y \<supseteq> set (map \<cdot> B @ D) \<Longrightarrow> X \<then> Y\<close>
proof (induct A B C D arbitrary: X Y rule: mp.induct)
  case (5 A B p q C)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set X\<close> \<open>set (map \<cdot> B) \<subseteq> set (p # Y)\<close>
    using 5(4,5) by auto
  moreover have \<open>set (map \<cdot> A @ C) \<subseteq> set (q # X)\<close> \<open>set (map \<cdot> B) \<subseteq> set Y\<close>
    using 5(4,5) by auto
  ultimately have \<open>(p \<rightarrow> q) # X \<then> Y\<close>
    using 5(1-3) by (simp add: Imp_L)
  then show ?case
    using 5(4) Set_L by fastforce
next
  case (6 A B C p q D)
  have \<open>set (map \<cdot> A @ C) \<subseteq> set (p # X)\<close> \<open>set (map \<cdot> B @ D) \<subseteq> set (q # Y)\<close>
    using 6(3,4) by auto
  then have \<open>X \<then> (p \<rightarrow> q) # Y\<close>
    using 6(1,2) by (simp add: Imp_R)
  then show ?case
    using 6(4) Set_R by fastforce
next
  case (7 A B)
  obtain n where \<open>n \<in> set A\<close> \<open>n \<in> set B\<close>
    using 7(1) by auto
  then have \<open>set (\<cdot>n # X) = set X\<close> \<open>set (\<cdot>n # Y) = set Y\<close>
    using 7(2,3) by auto
  then show ?case
    using Set_L Set_R Basic by metis
qed (use Fls_L Set_L in fastforce)+

theorem \<open>(\<forall>I. \<lbrakk>I\<rbrakk> X Y) \<longleftrightarrow> (X \<then> Y)\<close>
proof
  assume \<open>\<forall>I. \<lbrakk>I\<rbrakk> X Y\<close>
  then have \<open>mp [] [] X Y\<close>
    by (simp flip: main)
  then show \<open>X \<then> Y\<close>
    using MP by simp
qed (induct rule: SC.induct, auto)

end
