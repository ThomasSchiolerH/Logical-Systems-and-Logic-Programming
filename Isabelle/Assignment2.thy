theory Assignment2 imports Logic
begin

section \<open>Question 5\<close>

proposition \<open>[] \<then> ((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p # []\<close>
proof -
  from Imp_R have ?thesis if \<open>
    p # []
    \<then>
    ((p \<rightarrow> q) \<rightarrow> p) # []
    \<close>
    using that by force
  with Imp_R have ?thesis if \<open>
    (p \<rightarrow> q) #
    p # []
    \<then>
    p # []
    \<close>
    using that by force
  with Imp_L have ?thesis if \<open>
    ((p \<rightarrow> q) \<rightarrow> p) #
    (p \<rightarrow> q) #
    p # []
    \<then>
    p # []
    \<close>
    using that by force
  with Basic show ?thesis
    by force
qed

end
