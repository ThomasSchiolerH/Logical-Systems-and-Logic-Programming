theory Core_Logic_Assignment imports Core_Logic begin

proposition \<open>[] \<then> [(p \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> q] \<then> [p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p \<rightarrow> q, p] \<then> [q]\<close>
    using that by force
  from Basic have \<open>[p \<rightarrow> q, p] \<then> [q]\<close> by simp
  show ?thesis by force
qed


end
