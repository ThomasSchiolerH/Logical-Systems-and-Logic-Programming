theory Logic_Examples imports Logic begin

section \<open>Example 1\<close>

proposition \<open>p \<longrightarrow> p\<close> by fast

proposition \<open>[] \<then> (p \<rightarrow> p) # []\<close>
proof -
  from Imp_R have ?thesis if \<open>
    p # []
    \<then>
    p # []
    \<close>
    using that by force
  with Basic show ?thesis
    by force
qed

section \<open>Example 2\<close>

proposition \<open>p \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> q\<close> by fast

proposition \<open>[] \<then> (p \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q)) # []\<close>
proof -
  from Imp_R have ?thesis if \<open>
    p # []
    \<then>
    ((p \<rightarrow> q) \<rightarrow> q) # []
    \<close>
    using that by force
  with Imp_R have ?thesis if \<open>
    (p \<rightarrow> q) #
    p # []
    \<then>
    q # []
    \<close>
    using that by force
  with Imp_L have ?thesis if \<open>
    p # []
    \<then>
    p #
    q # []
    \<close> and \<open>
    q #
    p # []
    \<then>
    q # []
    \<close>
    using that by force
  with Basic show ?thesis
    by force
qed

section \<open>Example 3\<close>

proposition \<open>p \<longrightarrow> q \<longrightarrow> q \<longrightarrow> p\<close> by fast

proposition \<open>[] \<then> (p \<rightarrow> (q \<rightarrow> (q \<rightarrow> p))) # []\<close>
proof -
  from Imp_R have ?thesis if \<open>
    p # []
    \<then>
    (q \<rightarrow> (q \<rightarrow> p)) # []
    \<close>
    using that by force
  with Imp_R have ?thesis if \<open>
    q #
    p # []
    \<then>
    (q \<rightarrow> p) # []
    \<close>
    using that by force
  with Imp_R have ?thesis if \<open>
    q #
    q #
    p # []
    \<then>
    p # []
    \<close>
    using that by force
  with Set_L have ?thesis if \<open>
    p #
    q #
    q # []
    \<then>
    p # []
    \<close>
    using that by force
  with Basic show ?thesis
    by force
qed

section \<open>Example 4\<close>

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close> by fast

proposition \<open>p \<longrightarrow> (p \<longrightarrow> False) \<longrightarrow> False\<close> by fast

proposition \<open>[] \<then>  (p \<rightarrow> ((p \<rightarrow> \<bottom>) \<rightarrow> \<bottom>)) # []\<close>
proof -
  from Imp_R have ?thesis if \<open>
    p # []
    \<then>
    ((p \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) # []
    \<close>
    using that by force
  with Imp_R have ?thesis if \<open>
    (p \<rightarrow> \<bottom>) #
    p # []
    \<then>
    \<bottom> # []
    \<close>
    using that by force
  with Imp_L have ?thesis if \<open>
    p # []
    \<then>
    p #
    \<bottom> # []
    \<close> and \<open>
    \<bottom> #
    p # []
    \<then>
    \<bottom> # []
    \<close>
    using that by force
  with Basic show ?thesis
    by force
qed

end
