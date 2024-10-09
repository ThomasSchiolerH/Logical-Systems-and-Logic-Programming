theory Core_Logic_Appendix imports Core_Logic begin

proposition \<open>[] \<then> [p \<rightarrow> q \<rightarrow> p]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p] \<then> [q \<rightarrow> p]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[q, p] \<then> [p]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[p, q] \<then> [p]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed


proposition \<open>[] \<then> [(p \<rightarrow> r) \<rightarrow> (r \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
proof -
  from Imp_R have ?thesis if \<open>[p \<rightarrow> r] \<then> [(r \<rightarrow> q) \<rightarrow> p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[r \<rightarrow> q, p \<rightarrow> r] \<then> [p \<rightarrow> q]\<close>
    using that by force
  with Imp_R have ?thesis if \<open>[p, r \<rightarrow> q, p \<rightarrow> r] \<then> [q]\<close>
    using that by force
  with Set_L have ?thesis if \<open>[r \<rightarrow> q, p \<rightarrow> r, p] \<then> [q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p \<rightarrow> r, p] \<then> [r, q]\<close> and \<open>[q, p \<rightarrow> r, p] \<then> [q]\<close>
    using that by force
  with Basic have ?thesis if \<open>[p \<rightarrow> r, p] \<then> [r, q]\<close>
    using that by force
  with Imp_L have ?thesis if \<open>[p] \<then> [p, r, q]\<close> and \<open>[r, p] \<then> [r, q]\<close>
    using that by force
  with Basic show ?thesis
    by force
qed

end
